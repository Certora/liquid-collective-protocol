// Summaries for IDepositContract
// The Ethereum 2.0 Deposit Contract is an external actor (not part of the prover scene).
// All summaries use the wildcard receiver to match any instance of this interface.

methods {
    // get_deposit_root() returns the current Ethereum 2.0 deposit Merkle tree root.
    // Used by ConsensusLayerDepositManager as a front-running safety check.
    // Modeled as NONDET: returns an arbitrary bytes32, no side effects, no callbacks.
    function _.get_deposit_root() external => NONDET;

    // deposit() accepts exactly 32 ETH per validator call and activates the validator
    // on the Ethereum consensus layer. It is a one-way ETH sink: ETH is irreversibly
    // consumed and the deposit contract does not call back into River or any included
    // contract. Modeled as NONDET: ETH sent is consumed, no state side effects, no
    // callbacks (the NONDET "view summary" treatment prevents re-entrancy).
    function _.deposit(bytes, bytes, bytes, bytes32) external => NONDET;
}
