// use aiken/cbor
use aiken/collection/dict
use aiken/collection/list
use aiken/crypto.{ScriptHash, VerificationKeyHash}
use aiken/math/rational.{Rational}
use cardano/address.{Address, Script, VerificationKey}
use cardano/assets
use cardano/transaction.{
  InlineDatum, Input, Output, OutputReference, Transaction,
} as tx
use cardanocasino/types

validator cardanocasino(
  legitimacy_policy: ByteArray,
  legitimacy_name: ByteArray,
  intervals: List<types.Range>,
  game_token_policy: ByteArray,
  game_token_name: ByteArray,
) {
  spend(
    _datum: Option<types.Datum>,
    redeemer: types.Redeemer,
    output_ref: OutputReference,
    self: Transaction,
  ) {
    let Transaction { inputs, reference_inputs, outputs, .. } = self

    let val_hash = own_validator_script_address_hash(inputs, output_ref)

    let script_inputs = get_script_inputs(inputs, val_hash)

    expect Some(first_input) = list.head(script_inputs)

    if output_ref == first_input.output_reference {
      when redeemer is {
        types.FulfilBet(rn_numerator, rn_denominator) -> {
          expect Some(random_number) =
            rational.new(rn_numerator, rn_denominator)

          let multiplier = get_multiplier(random_number, intervals)

          let bet_inputs = get_bet_inputs(script_inputs)
          let only_one_bet = list.length(bet_inputs) == 1

          let only_bet_or_bank =
            list.all(
              script_inputs,
              fn(input) {
                expect InlineDatum(data) = input.output.datum
                expect datum: types.Datum = data
                when datum is {
                  types.Bank -> True
                  types.Bet(..) -> True
                  _ -> False
                }
              },
            )

          let bet_input_option = list.head(bet_inputs)
          expect Some(bet_input) = bet_input_option
          expect InlineDatum(data) = bet_input.output.datum
          expect datum: types.Datum = data
          expect types.Bet(owner, amount) = datum

          let bet_atleast_minimum = check_bet_minimum(game_token_policy, amount)

          let user_amount =
            amount + rational.floor(
              rational.mul(
                rational.sub(multiplier, rational.from_int(1)),
                rational.from_int(amount),
              ),
            )
          let bank_amount = -user_amount + amount

          let amount_sent_to_bet_owner =
            tokens_sent_to_address(
              inputs,
              outputs,
              game_token_policy,
              game_token_name,
              owner,
            )
          let correct_amount_sent_to_owner =
            amount_sent_to_bet_owner >= user_amount

          let amount_sent_to_bank =
            tokens_sent_to_bank(
              inputs,
              outputs,
              game_token_policy,
              game_token_name,
              val_hash,
            )
          let correct_amount_sent_to_bank = amount_sent_to_bank >= bank_amount
          // trace cbor.diagnostic(amount_sent_to_bank)
          // trace cbor.diagnostic(bank_amount)
          let valid_tokens_sent_to_bank =
            check_tokens_sent_to_bank(
              outputs,
              game_token_policy,
              game_token_name,
              val_hash,
            )

          let admin_datum =
            get_admin_data(
              reference_inputs,
              val_hash,
              legitimacy_policy,
              legitimacy_name,
            )
          expect types.AdminData(_, fee, fee_address, backend_key) = admin_datum

          let no_other_scripts =
            check_no_other_scripts(inputs, val_hash, backend_key)

          let fee_paid =
            lovelace_sent_to_address(inputs, outputs, fee_address) >= fee

          let bet_utxo_correct_amount =
            assets.lovelace_of(bet_input.output.value) >= get_min_utxo_lovelace(game_token_policy, amount, fee)

          let tx_signed_by_backend =
            list.has(self.extra_signatories, backend_key)
          only_bet_or_bank? && only_one_bet? && bet_atleast_minimum? && correct_amount_sent_to_owner? && correct_amount_sent_to_bank? && valid_tokens_sent_to_bank? && tx_signed_by_backend? && fee_paid? && no_other_scripts? && bet_utxo_correct_amount?
        }
        types.WithdrawBank -> {
          let admin_datum =
            get_admin_data(
              reference_inputs,
              val_hash,
              legitimacy_policy,
              legitimacy_name,
            )
          expect types.AdminData(admin_keys, ..) = admin_datum

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

          let quorum_reached = check_quorum(admin_keys, self)
          only_bank_inputs && quorum_reached
        }
        types.UpdateAdminData -> {
          let script_inputs = get_script_inputs(inputs, val_hash)

          let only_one_input = list.length(script_inputs) == 1
          let admin_datum =
            get_admin_data(
              script_inputs,
              val_hash,
              legitimacy_policy,
              legitimacy_name,
            )
          expect types.AdminData(admin_keys, ..) = admin_datum
          let quorum_reached = check_quorum(admin_keys, self)

          let script_outputs =
            list.filter(
              outputs,
              fn(output) {
                output.address == Address {
                  payment_credential: Script(val_hash),
                  stake_credential: None,
                } && assets.quantity_of(
                  output.value,
                  legitimacy_policy,
                  legitimacy_name,
                ) == 1 && assets.policies(output.value) == [
                  #"", legitimacy_policy,
                ]
              },
            )
          let only_one_script_output = list.length(script_outputs) == 1

          let output_valid =
            list.all(
              script_outputs,
              fn(output) {
                expect InlineDatum(data) = output.datum
                expect datum: types.Datum = data
                when datum is {
                  types.AdminData(..) ->
                    assets.quantity_of(
                      output.value,
                      legitimacy_policy,
                      legitimacy_name,
                    ) == 1 && assets.policies(output.value) == [
                      #"", legitimacy_policy,
                    ]
                  _ -> False
                }
              },
            )

          only_one_input? && quorum_reached? && only_one_script_output? && output_valid?
        }
      }
    } else {
      True
    }
  }

  else(_) {
    fail
  }
}

fn own_validator_script_address_hash(
  inputs: List<Input>,
  output_reference: OutputReference,
) -> ScriptHash {
  expect Some(input) =
    list.find(inputs, fn(input) { input.output_reference == output_reference })
  expect Script(hash) = input.output.address.payment_credential

  hash
}

fn get_script_inputs(inputs: List<Input>, val_hash: ScriptHash) -> List<Input> {
  let script_inputs =
    list.filter(
      inputs,
      fn(input) { input.output.address.payment_credential == Script(val_hash) },
    )

  script_inputs
}

fn check_no_other_scripts(
  inputs: List<Input>,
  val_hash: ScriptHash,
  backend_key: VerificationKeyHash,
) -> Bool {
  list.all(
    inputs,
    fn(input) {
      input.output.address.payment_credential == VerificationKey(backend_key) || input.output.address.payment_credential == Script(
        val_hash,
      )
    },
  )
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

fn lovelace_sent_to_address(
  inputs: List<Input>,
  outputs: List<Output>,
  address: Address,
) -> Int {
  let inputs_from_address =
    list.filter(inputs, fn(input) { input.output.address == address })
  let ada_from_address =
    list.foldl(
      inputs_from_address,
      0,
      fn(input, total) { total + assets.lovelace_of(input.output.value) },
    )
  let outputs_to_address =
    list.filter(outputs, fn(output) { output.address == address })

  let ada_to_address =
    list.foldl(
      outputs_to_address,
      0,
      fn(output, total) { total + assets.lovelace_of(output.value) },
    )

  ada_to_address - ada_from_address
}

fn tokens_sent_to_address(
  inputs: List<Input>,
  outputs: List<Output>,
  game_token_policy: ByteArray,
  game_token_name: ByteArray,
  address: Address,
) -> Int {
  let inputs_from_address =
    list.filter(inputs, fn(input) { input.output.address == address })
  let tokens_from_address =
    list.foldl(
      inputs_from_address,
      0,
      fn(input, total) {
        total + assets.quantity_of(
          input.output.value,
          game_token_policy,
          game_token_name,
        )
      },
    )
  let outputs_to_address =
    list.filter(outputs, fn(output) { output.address == address })

  let tokens_to_address =
    list.foldl(
      outputs_to_address,
      0,
      fn(output, total) {
        total + assets.quantity_of(
          output.value,
          game_token_policy,
          game_token_name,
        )
      },
    )

  tokens_to_address - tokens_from_address
}

fn tokens_sent_to_bank(
  inputs: List<Input>,
  outputs: List<Output>,
  game_token_policy: ByteArray,
  game_token_name: ByteArray,
  val_hash: ScriptHash,
) -> Int {
  let inputs_from_bank =
    list.filter(
      inputs,
      fn(input) {
        input.output.address.payment_credential == Script(val_hash) && input.output.datum == InlineDatum(
          types.Bank,
        )
      },
    )
  let tokens_from_bank =
    list.foldl(
      inputs_from_bank,
      0,
      fn(input, total) {
        total + assets.quantity_of(
          input.output.value,
          game_token_policy,
          game_token_name,
        )
      },
    )
  let outputs_to_bank =
    list.filter(
      outputs,
      fn(output) {
        output.address.payment_credential == Script(val_hash) && output.datum == InlineDatum(
          types.Bank,
        )
      },
    )

  let tokens_to_bank =
    list.foldl(
      outputs_to_bank,
      0,
      fn(output, total) {
        total + assets.quantity_of(
          output.value,
          game_token_policy,
          game_token_name,
        )
      },
    )

  tokens_to_bank - tokens_from_bank
}

fn check_tokens_sent_to_bank(
  outputs: List<Output>,
  game_token_policy: ByteArray,
  game_token_name: ByteArray,
  val_hash: ScriptHash,
) {
  let outputs_to_bank =
    list.filter(
      outputs,
      fn(output) {
        output.address.payment_credential == Script(val_hash) && output.datum == InlineDatum(
          types.Bank,
        )
      },
    )
  list.all(
    outputs_to_bank,
    fn(output) {
      let only_expected_policies =
        assets.policies(output.value) == list.unique([#"", game_token_policy])

      let token_names =
        assets.tokens(output.value, game_token_policy)
          |> dict.keys()
      let only_expected_tokens = token_names == [game_token_name]

      only_expected_policies? && only_expected_tokens?
    },
  )
}

fn get_min_utxo_lovelace(
  game_token_policy: ByteArray,
  amount: Int,
  fee_amount: Int
) -> Int {
  when game_token_policy is {
    "" -> amount + fee_amount
    _ -> fee_amount + 1_000_000
  }
}

fn check_bet_minimum(
  game_token_policy: ByteArray,
  amount: Int
) -> Bool {
  when game_token_policy is {
    "" -> amount >= 1_000_000
    _ -> amount >= 1
  }
}

fn get_admin_data(
  inputs: List<Input>,
  val_hash: ScriptHash,
  legitimacy_policy: ByteArray,
  legitimacy_name: ByteArray,
) -> types.Datum {
  let script_inputs =
    list.filter(
      inputs,
      fn(input) { input.output.address.payment_credential == Script(val_hash) },
    )

  let admin_data_inputs =
    list.filter(
      script_inputs,
      fn(input) {
        expect InlineDatum(data) = input.output.datum
        expect datum: types.Datum = data
        when datum is {
          types.AdminData(..) ->
            assets.quantity_of(
              input.output.value,
              legitimacy_policy,
              legitimacy_name,
            ) == 1
          _ -> False
        }
      },
    )

  if list.length(admin_data_inputs) != 1 {
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

fn check_quorum(admin_keys: List<VerificationKeyHash>, transaction: Transaction) {
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
  signature_amounts >= quorum_amount
}

// Get Multiplier.
// This function gets the multiplier to be applied to the user's bet based on the random number generated by the game
// This random number is a rational number (a decimal 0-1 is created by the backend which is then split into a numerator and denominator and recombined within the script)
// The upper and lower limits for each multiplier are parameters of the script
fn get_multiplier(
  random_number: Rational,
  intervals: List<types.Range>,
) -> Rational {
  // trace cbor.diagnostic(intervals)

  expect Some(range) =
    list.find(
      intervals,
      fn(range) {
        expect Some(interval_lower) =
          rational.new(range.lower_numerator, range.lower_denominator)
        expect Some(interval_upper) =
          rational.new(range.upper_numerator, range.upper_denominator)
        rational.compare_with(random_number, >, interval_lower) && rational.compare_with(
          random_number,
          <=,
          interval_upper,
        )
      },
    )

  //return the multiplier
  if range.multiplier_numerator >= 0 && range.multiplier_denominator > 0 {
    expect Some(multiplier) =
      rational.new(range.multiplier_numerator, range.multiplier_denominator)
    multiplier
  } else {
    fail @"Invalid Multiplier"
  }
}

test check_multiplier() {
  let intervals =
    [
      types.Range {
        multiplier_numerator: 0,
        multiplier_denominator: 1,
        lower_numerator: 0,
        lower_denominator: 1,
        upper_numerator: 5,
        upper_denominator: 10,
      },
      types.Range {
        multiplier_numerator: 39,
        multiplier_denominator: 20,
        lower_numerator: 5,
        lower_denominator: 10,
        upper_numerator: 1,
        upper_denominator: 1,
      },
    ]
  expect Some(test_rn) = rational.new(1, 10)

  //2
  let multiplier = get_multiplier(test_rn, intervals)
  // expect(multiplier) = rational.new(39,20)
  //10 ada
  let amount = 15_000_000

  let user_amount =
    amount + rational.floor(
      rational.mul(
        rational.sub(multiplier, rational.from_int(1)),
        rational.from_int(amount),
      ),
    )
  let bank_amount = -user_amount + amount

  (user_amount == 0_000_000)? && (bank_amount == 15_000_000)?
}
