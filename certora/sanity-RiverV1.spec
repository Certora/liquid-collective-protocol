import "./RiverV1_call_resolution.spec";
//use builtin rule sanity;

// turns out some codes do have an 'f'! e.g. Cork
rule sanity (method certoraF) filtered {
    certoraF -> certoraF.selector != sig:depositToConsensusLayerWithAttestation(bytes32,bytes32,bytes[],BLS12_381.DepositY[]).selector
              && certoraF.selector != sig:validate(bytes32,bytes32,bytes[],BLS12_381.DepositY[],bytes32).selector
              && certoraF.selector != sig:verifyBLSDeposit(bytes,bytes,uint256,BLS12_381.DepositY,bytes32).selector // needs loop iter 7
} {
    env e;
    calldataarg args;
    certoraF(e, args);
    satisfy true, "sanity check failed";
}
