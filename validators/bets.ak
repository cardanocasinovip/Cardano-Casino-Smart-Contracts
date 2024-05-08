use aiken/cbor
use aiken/hash.{Blake2b_224, Hash}
use aiken/list
use aiken/math/rational
use aiken/transaction.{
  InlineDatum, Input, Output, OutputReference, ScriptContext, Spend, Transaction,
} as tx
use aiken/transaction/credential.{
  Address, Script, ScriptCredential, VerificationKey, VerificationKeyCredential,
}
use aiken/transaction/value
use cardanocasino/types

validator(legitimacy_policy: ByteArray, legitimacy_name: ByteArray) {
  fn spend(
    _datum: types.Datum,
    redeemer: types.Redeemer,
    ctx: ScriptContext,
  ) -> Bool {
    let ScriptContext { transaction, purpose } = ctx

    expect Spend(output_ref) = purpose

    let Transaction { inputs, reference_inputs, outputs, .. } = transaction

    let val_hash = own_validator_script_address_hash(inputs, output_ref)

    when redeemer is {
      types.FulfilBet(user_amount, bank_amount) -> {
        let script_inputs = get_script_inputs(inputs, val_hash)
        let bet_inputs = get_bet_inputs(script_inputs)
        let only_one_bet = list.length(bet_inputs) == 1

        let bet_input_option = list.head(bet_inputs)
        expect Some(bet_input) = bet_input_option
        expect InlineDatum(data) = bet_input.output.datum
        expect datum: types.Datum = data
        expect types.Bet(owner, amount) = datum

        let amount_sent_to_bet_owner =
          lovelace_sent_to_pkh(inputs, outputs, owner)

        let correct_amount_sent_to_owner =
          atleast(amount_sent_to_bet_owner, user_amount)
        let amount_sent_to_bank =
          lovelace_sent_to_bank(inputs, outputs, val_hash)

        let correct_amount_sent_to_bank = amount_sent_to_bank >= bank_amount

        let admin_datum =
          get_admin_data(
            reference_inputs,
            val_hash,
            legitimacy_policy,
            legitimacy_name,
          )
        expect types.AdminData(_, fee, fee_address, backend_key) = admin_datum

        expect Some(fee_rational) = rational.new(fee, 100)

        let amount_rational = rational.from_int(amount)

        let fee_amount_rational = rational.mul(fee_rational, amount_rational)
        let actual_fee = rational.ceil(fee_amount_rational)

        let fee_paid =
          atleast(
            lovelace_sent_to_pkh(inputs, outputs, fee_address),
            actual_fee,
          )

        let tx_signed_by_backend =
          list.has(transaction.extra_signatories, backend_key)
        only_one_bet? && correct_amount_sent_to_owner? && correct_amount_sent_to_bank? && tx_signed_by_backend? && fee_paid?
      }
      types.WithdrawBank -> {
        let admin_datum =
          get_admin_data(
            reference_inputs,
            val_hash,
            legitimacy_policy,
            legitimacy_name,
          )
        expect types.AdminData(admin_keys, _, _, _) = admin_datum

        let script_inputs = get_script_inputs(inputs, val_hash)
        let only_bank_inputs =
          list.all(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data
              when datum is {
                types.Bank -> True
                _ -> False
              }
            },
          )

        let quorum_amount = list.length(admin_keys) / 2 + 1
        let signature_amounts =
          list.foldl(
            admin_keys,
            0,
            fn(key, total) {
              if list.has(transaction.extra_signatories, key) {
                total + 1
              } else {
                total
              }
            },
          )
        only_bank_inputs && signature_amounts >= quorum_amount
      }
      types.UpdateAdminData(
        new_admin_keys,
        new_fee,
        new_fee_address,
        new_backend_key,
      ) -> {
        let script_inputs = get_script_inputs(inputs, val_hash)
        let admin_inputs =
          list.filter(
            script_inputs,
            fn(input) {
              expect InlineDatum(data) = input.output.datum
              expect datum: types.Datum = data
              when datum is {
                types.AdminData(..) ->
                  input.output.address == Address {
                    payment_credential: ScriptCredential(val_hash),
                    stake_credential: None,
                  } && value.quantity_of(
                    input.output.value,
                    legitimacy_policy,
                    legitimacy_name,
                  ) == 1
                _ -> False
              }
            },
          )
        let only_admin_input = admin_inputs == script_inputs

        let only_one_admin_input = list.length(admin_inputs) == 1
        let admin_datum =
          get_admin_data(
            admin_inputs,
            val_hash,
            legitimacy_policy,
            legitimacy_name,
          )
        expect types.AdminData(admin_keys, _, _, _) = admin_datum

        let quorum_amount = list.length(admin_keys) / 2 + 1
        let signature_amounts =
          list.foldl(
            admin_keys,
            0,
            fn(key, total) {
              if list.has(transaction.extra_signatories, key) {
                total + 1
              } else {
                total
              }
            },
          )
        let script_outputs =
          list.filter(
            outputs,
            fn(output) {
              output.address == Address {
                payment_credential: ScriptCredential(val_hash),
                stake_credential: None,
              }
            },
          )
        let only_one_script_output = list.length(script_outputs) == 1

        let output_correct =
          list.all(
            script_outputs,
            fn(output) {
              expect InlineDatum(data) = output.datum
              expect datum: types.Datum = data
              when datum is {
                types.AdminData(admin_keys, fee, fee_address, backend_key) ->
                  admin_keys == new_admin_keys && fee == new_fee && fee_address == new_fee_address && backend_key == new_backend_key && value.quantity_of(
                    output.value,
                    legitimacy_policy,
                    legitimacy_name,
                  ) == 1
                _ -> False
              }
            },
          )

        only_admin_input? && only_one_admin_input? && signature_amounts >= quorum_amount? && only_one_script_output? && output_correct?
      }
    }
  }
}

fn own_validator_script_address_hash(
  inputs: List<Input>,
  output_reference: OutputReference,
) -> Hash<Blake2b_224, Script> {
  expect Some(input) =
    list.find(inputs, fn(input) { input.output_reference == output_reference })
  expect ScriptCredential(hash) = input.output.address.payment_credential

  hash
}

fn get_script_inputs(
  inputs: List<Input>,
  val_hash: Hash<Blake2b_224, Script>,
) -> List<Input> {
  let script_inputs =
    list.filter(
      inputs,
      fn(input) {
        input.output.address == Address {
          payment_credential: ScriptCredential(val_hash),
          stake_credential: None,
        }
      },
    )

  script_inputs
}

fn get_bet_inputs(script_inputs: List<Input>) -> List<Input> {
  let bet_inputs =
    list.filter(
      script_inputs,
      fn(input) {
        expect InlineDatum(data) = input.output.datum
        expect datum: types.Datum = data
        when datum is {
          types.Bet(..) -> True
          _ -> False
        }
      },
    )
  bet_inputs
}

fn lovelace_sent_to_pkh(
  inputs: List<Input>,
  outputs: List<Output>,
  pkh: Hash<Blake2b_224, VerificationKey>,
) -> Int {
  let inputs_from_pkh =
    list.filter(
      inputs,
      fn(input) {
        input.output.address.payment_credential == VerificationKeyCredential(
          pkh,
        )
      },
    )
  let ada_from_pkh =
    list.foldl(
      inputs_from_pkh,
      0,
      fn(input, total) { total + value.lovelace_of(input.output.value) },
    )
  let outputs_to_pkh =
    list.filter(
      outputs,
      fn(output) {
        output.address.payment_credential == VerificationKeyCredential(pkh)
      },
    )

  let ada_to_pkh =
    list.foldl(
      outputs_to_pkh,
      0,
      fn(output, total) { total + value.lovelace_of(output.value) },
    )

  ada_to_pkh - ada_from_pkh
}

fn lovelace_sent_to_bank(
  inputs: List<Input>,
  outputs: List<Output>,
  val_hash: Hash<Blake2b_224, Script>,
) -> Int {
  let inputs_from_bank =
    list.filter(
      inputs,
      fn(input) {
        input.output.address == Address {
          payment_credential: ScriptCredential(val_hash),
          stake_credential: None,
        } && input.output.datum == InlineDatum(types.Bank)
      },
    )
  let ada_from_bank =
    list.foldl(
      inputs_from_bank,
      0,
      fn(input, total) { total + value.lovelace_of(input.output.value) },
    )
  let outputs_to_bank =
    list.filter(
      outputs,
      fn(output) {
        output.address == Address {
          payment_credential: ScriptCredential(val_hash),
          stake_credential: None,
        } && output.datum == InlineDatum(types.Bank)
      },
    )

  let ada_to_bank =
    list.foldl(
      outputs_to_bank,
      0,
      fn(output, total) { total + value.lovelace_of(output.value) },
    )

  ada_to_bank - ada_from_bank
}

fn atleast(amount: Int, target: Int) -> Bool {
  if target < 0 {
    amount <= target
  } else {
    amount >= target
  }
}

fn get_admin_data(
  inputs: List<Input>,
  val_hash: Hash<Blake2b_224, Script>,
  legitimacy_policy: ByteArray,
  legitimacy_name: ByteArray,
) -> types.Datum {
  let admin_data_inputs =
    list.filter(
      inputs,
      fn(input) {
        expect InlineDatum(data) = input.output.datum
        expect datum: types.Datum = data
        when datum is {
          types.AdminData(..) ->
            input.output.address.payment_credential == ScriptCredential(
              val_hash,
            ) && value.quantity_of(
              input.output.value,
              legitimacy_policy,
              legitimacy_name,
            ) == 1
          _ -> False
        }
      },
    )

  if list.length(admin_data_inputs) != 1 {
    trace cbor.diagnostic(list.length(admin_data_inputs))
    fail @"Multiple or no AdminData datums found"
  } else {
    let admin_data_input_option = list.head(admin_data_inputs)
    expect Some(admin_data_input) = admin_data_input_option
    expect InlineDatum(data) = admin_data_input.output.datum
    expect datum: types.Datum = data
    expect types.AdminData(..) = datum

    datum
  }
}
