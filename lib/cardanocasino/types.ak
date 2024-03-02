use aiken/hash.{Blake2b_224, Hash}
use aiken/transaction/credential.{Script, VerificationKey}

pub type Datum {
  Deposit { owner: Hash<Blake2b_224, VerificationKey> }
  Bank
  UpdateRequest {
    user_pkh: Hash<Blake2b_224, VerificationKey>,
    user_amount: Int,
    bank_amount: Int,
    random_number: ByteArray,
    game: ByteArray,
    timestamp: ByteArray,
  }
}

pub type Redeemer {
  Update
  Withdraw
}

pub type ValidatorHash =
  Hash<Blake2b_224, Script>
