use aiken/bytearray
use aiken/dict
use aiken/list
use aiken/string
use aiken/transaction.{
  InlineDatum, Input, OutputReference, ScriptContext, Spend, Transaction,
} as tx
use aiken/transaction/credential.{ScriptCredential}
use aiken/transaction/value
use cardanocasino/types

validator {
  fn spend(
    _datum: types.Datum,
    redeemer: types.Redeemer,
    ctx: ScriptContext,
  ) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Spend(output_ref) = purpose

    let Transaction { inputs, outputs, .. } = transaction

    let val_hash = own_validator_script_address_hash(inputs, output_ref)

    // Get inputs that have come from the script
    let script_inputs =
      list.filter(
        inputs,
        fn(input) {
          input.output.address.payment_credential == ScriptCredential(val_hash)
        },
      )

    // Filter script_inputs for inputs that have the Bank datum
    let bank_inputs =
      list.filter(
        script_inputs,
        fn(input) { input.output.datum == InlineDatum(types.Bank) },
      )

    // Get outputs that are sent back to the script with the Bank datum
    let bank_outputs =
      list.filter(
        outputs,
        fn(output) {
          output.address.payment_credential == ScriptCredential(val_hash) && output.datum == InlineDatum(
            types.Bank,
          )
        },
      )
    // Get the amount of ada in the Bank inputs
    let bank_input_ada =
      list.foldl(
        bank_inputs,
        0,
        fn(input, amnt) { amnt + value.lovelace_of(input.output.value) },
      )

    // Get the amount of ada in the Bank outputs
    let bank_output_ada =
      list.foldl(
        bank_outputs,
        0,
        fn(output, amnt) { amnt + value.lovelace_of(output.value) },
      )

    when redeemer is {
      types.Update -> {
        let requests =
          list.filter(
            script_inputs,
            fn(input) {
              trace @"redeemer is update"
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data

              when datum is {
                types.UpdateRequest(..) ->
                  // Check the transaction has been verified by the Cardano Casino backend
                  list.has(
                    transaction.extra_signatories,
                    #"b0a90114f918987398275998d2143e38d18bbeaf58772bf39f326e1c",
                  )
                _ -> False
              }
            },
          )

        // Sort the requests so there are less outputs going back to the script
        let sorted_requests =
          list.foldl(
            requests,
            dict.new(),
            fn(request, sorted) {
              trace @"sorting requests"
              expect InlineDatum(data) = request.output.datum
              expect datum: types.Datum = data
              expect types.UpdateRequest(user_pkh, user_amount, bank_amount, ..) =
                datum
              if dict.has_key(sorted, user_pkh) {
                expect Some([user_amnt, bank_amnt]) =
                  dict.get(sorted, key: user_pkh)
                let sorted =
                  dict.insert(
                    sorted,
                    key: user_pkh,
                    value: [user_amnt + user_amount, bank_amnt + bank_amount],
                    compare: bytearray.compare,
                  )
                sorted
              } else {
                let sorted =
                  dict.insert(
                    sorted,
                    key: user_pkh,
                    value: [user_amount, bank_amount],
                    compare: bytearray.compare,
                  )
                sorted
              }
            },
          )

        // Check that all input requests have been satisfied. 
        let all_users_updated =
          list.all(
            dict.to_list(sorted_requests),
            fn(request) {
              let (user_pkh, values) = request
              expect [user_amount, _] = values
              let user_inputs =
                list.filter(
                  inputs,
                  fn(input) {
                    input.output.address.payment_credential == ScriptCredential(
                      val_hash,
                    ) && input.output.datum == InlineDatum(
                      types.Deposit { owner: user_pkh },
                    )
                  },
                )
              let user_outputs =
                list.filter(
                  outputs,
                  fn(output) {
                    output.address.payment_credential == ScriptCredential(
                      val_hash,
                    ) && output.datum == InlineDatum(
                      types.Deposit { owner: user_pkh },
                    )
                  },
                )
              let user_input_ada =
                list.foldl(
                  user_inputs,
                  0,
                  fn(input, amnt) {
                    amnt + value.lovelace_of(input.output.value)
                  },
                )

              let user_output_ada =
                list.foldl(
                  user_outputs,
                  0,
                  fn(output, amnt) { amnt + value.lovelace_of(output.value) },
                )
              trace string.from_int(user_output_ada)
              trace string.from_int(user_input_ada)
              trace string.from_int(user_amount)
              (user_output_ada - user_input_ada == user_amount)?
            },
          )

        let bank_amount =
          list.foldl(
            dict.to_list(sorted_requests),
            0,
            fn(request, amnt) {
              let (_, values) = request
              expect [_, bank_amount] = values

              amnt + bank_amount
            },
          )

        let bank_updated = bank_output_ada - bank_input_ada == bank_amount

        all_users_updated? && bank_updated?
      }

      types.Withdraw -> {
        let user_withdrawal =
          list.all(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data
              expect types.Deposit(owner) = datum

              // Check the transaction was signed by the user who owns the funds
              list.has(transaction.extra_signatories, owner) == True
            },
          )
        let bank_withdrawal =
          list.all(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data

              // Check only Bank funds are withdrawn and it is signed by the CC wallet
              datum == types.Bank && list.has(
                transaction.extra_signatories,
                #"b0a90114f918987398275998d2143e38d18bbeaf58772bf39f326e1c",
              )
            },
          )
        user_withdrawal || bank_withdrawal
      }
    }
  }
}

fn own_validator_script_address_hash(
  inputs: List<Input>,
  output_reference: OutputReference,
) -> types.ValidatorHash {
  expect Some(input) =
    list.find(inputs, fn(input) { input.output_reference == output_reference })
  expect ScriptCredential(hash) = input.output.address.payment_credential

  hash
}
