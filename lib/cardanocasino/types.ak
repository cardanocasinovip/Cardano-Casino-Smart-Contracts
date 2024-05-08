use aiken/hash.{Blake2b_224, Hash}
use aiken/transaction/credential.{VerificationKey}

pub type Datum {
  // utxo containing the administrative data such as admin keys
  AdminData {
    admin_keys: List<Hash<Blake2b_224, VerificationKey>>,
    fee: Int,
    fee_address: Hash<Blake2b_224, VerificationKey>,
    backend_key: Hash<Blake2b_224, VerificationKey>,
  }
  //bank utxos
  Bank
  // utxo containing a user's bet
  Bet { owner: Hash<Blake2b_224, VerificationKey>, amount: Int }
}

pub type Redeemer {
  // fulfil a bet with either a win or a loss. Contains the amount of ada the user will receive and the amount of ada the bank will receive.
  FulfilBet { user_amount: Int, bank_amount: Int }
  // redeemer to withdraw funds from the bank
  WithdrawBank
  // redeemer to update the admin data.
  UpdateAdminData {
    new_admin_keys: List<Hash<Blake2b_224, VerificationKey>>,
    new_fee: Int,
    new_fee_address: Hash<Blake2b_224, VerificationKey>,
    new_backend_key: Hash<Blake2b_224, VerificationKey>,
  }
}
