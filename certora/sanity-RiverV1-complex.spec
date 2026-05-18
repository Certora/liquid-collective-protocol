import "./RiverV1_call_resolution.spec";
import "specs/summaries/RiverV1_base_summaries.spec";


// Sanity over the two BLS-heavy entry points only, for complexity-reduction experiments.
// verifyBLSDeposit is excluded here because it only needs a higher loop_iter, not complexity work.
rule sanityBLSDeposit (method certoraF) filtered {
    // certoraF -> certoraF.selector == sig:validate(bytes32,bytes32,bytes[],BLS12_381.DepositY[],bytes32).selector
    certoraF -> certoraF.selector == sig:depositToConsensusLayerWithAttestation(bytes32,bytes32,bytes[],BLS12_381.DepositY[]).selector
} {
    env e;
    calldataarg args;
    certoraF(e, args);
    satisfy true, "sanity check failed";
}

// Sanity over verifyBLSDeposit only. Needs a higher loop_iter (see note above).
rule sanityVerifyBLSDeposit (method certoraF) filtered {
    certoraF -> certoraF.selector == sig:verifyBLSDeposit(bytes,bytes,uint256,BLS12_381.DepositY,bytes32).selector
} {
    env e;
    calldataarg args;
    certoraF(e, args);
    satisfy true, "sanity check failed";
}