# Cardano Casino Smart Contracts

## Datums

### Deposit
  The deposit datum is used when a player is depositing their funds into the contract and contains the player's public key hash to identifiy their funds. It has the following definition:
  
  ```Deposit { owner: Hash<Blake2b_224, VerificationKey> }```

### Bank
  The Bank datum is used to identify funds that belong tho the smart contract bank. It contains no extra information.

### Update Request
  The Update Request datum is used when a player plays a game on the CardanoCasino website. It contains information about the player and the bet. It is defined below:
  
  ```
  UpdateRequest {
    user_pkh: Hash<Blake2b_224, VerificationKey>,
    user_amount: Int,
    bank_amount: Int,
    signature: ByteArray,
    random_number: ByteArray,
    game: ByteArray,
    timestamp: ByteArray,
  }
  ```

## Redeemers

### Update
  The Update redeemer is used when player's balances are being updated. It checks that the update has been signed by our backend server, ensuring that no malicious actors can alter funds.

### Withdraw
  The Withdraw redeemer is used when a player would like to remove funds from the contract, or bank funds are removed by Cardano Casino. This ensures that the owner of the funds has signed the transaction, verifying that it is indeed them that has withdrawn the funds.
