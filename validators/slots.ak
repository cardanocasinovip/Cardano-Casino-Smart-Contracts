use aiken/bytearray
use aiken/dict
use aiken/hash
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

    let script_inputs =
      list.filter(
        inputs,
        fn(input) {
          input.output.address.payment_credential == ScriptCredential(val_hash)
        },
      )

    let bank_inputs =
      list.filter(
        inputs,
        fn(input) {
          input.output.address.payment_credential == ScriptCredential(val_hash) && input.output.datum == InlineDatum(
            types.Bank,
          )
        },
      )
    let bank_outputs =
      list.filter(
        outputs,
        fn(output) {
          output.address.payment_credential == ScriptCredential(val_hash) && output.datum == InlineDatum(
            types.Bank,
          )
        },
      )
    let bank_input_ada =
      list.foldl(
        bank_inputs,
        0,
        fn(input, amnt) { amnt + value.lovelace_of(input.output.value) },
      )

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
                types.UpdateRequest(_, user_amount, bank_amount, signature) -> {
                  let message =
                    string.join(
                      [
                        @"User:",
                        string.from_int(user_amount),
                        @"Bank:",
                        string.from_int(bank_amount),
                      ],
                      @" ",
                    )
                  let correct_signature =
                    signature == hash.sha3_256(
                      bytearray.concat(
                        string.to_bytearray(message),
                        string.to_bytearray(
                          @"afd8aa6a-710e-4e19-afdc-4a025025399c",
                        ),
                      ),
                    )

                  if correct_signature {
                    True
                  } else {
                    fail @"Invalid signature in inputs"
                  }
                }
                _ -> False
              }
            },
          )

        let sorted_requests =
          list.foldl(
            requests,
            dict.new(),
            fn(request, sorted) {
              trace @"sorting requests"
              expect InlineDatum(data) = request.output.datum
              expect datum: types.Datum = data
              expect types.UpdateRequest(user_pkh, user_amount, bank_amount, _) =
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
                    input.output.address.payment_credential == ScriptCredential(val_hash) && input.output.datum == InlineDatum(
                      types.Deposit { owner: user_pkh },
                    )
                  },
                )
              let user_outputs =
                list.filter(
                  outputs,
                  fn(output) {
                    output.address.payment_credential == ScriptCredential(val_hash) && output.datum == InlineDatum(
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
        let script_inputs =
          list.filter(
            inputs,
            fn(input) {
              input.output.address.payment_credential == ScriptCredential(
                val_hash,
              )
            },
          )

        let user_withdrawal =
          list.all(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data
              expect types.Deposit(_) = datum

              list.has(
                transaction.extra_signatories,
                #"b0a90114f918987398275998d2143e38d18bbeaf58772bf39f326e1c",
              ) == True
            },
          )
        let bank_withdrawal =
          list.all(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data

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
