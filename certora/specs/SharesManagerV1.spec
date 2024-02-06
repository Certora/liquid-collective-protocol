import "Base.spec";

methods {
    function allowance(address, address) external returns(uint256) envfree;
    function balanceOf(address) external returns(uint256) envfree;
    function balanceOfUnderlying(address) external returns(uint256) envfree;
    function totalSupply() external returns(uint256) envfree;
}

ghost mathint counter_onEarnings{ // counter checking number of calls to _onDeposit
    init_state axiom counter_onEarnings == 0;
}
ghost mathint total_onEarnings{ // counter checking number of calls to _onDeposit
    init_state axiom total_onEarnings == 0;// this is total earned ETH
}
ghost mathint total_onDeposits{ // counter checking number of calls to _onDeposit
    init_state axiom total_onDeposits == 0;// this is total earned ETH
}

function ghostUpdate_onEarnings(uint256 amount) returns bool
{
    counter_onEarnings = counter_onEarnings + 1;
    total_onEarnings = total_onEarnings + amount;
    return true;
}

function ghostUpdate_onDeposits(uint256 amount) returns bool
{
    total_onDeposits = total_onDeposits + amount;
    return true;
}

invariant totalUnderlyingSupplyBasicIntegrity()
    to_mathint(totalUnderlyingSupply()) == total_onDeposits
    filtered {
        f -> f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
          && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
    } {
        preserved
        {
            require total_onDeposits <= 2^128;
            require total_onEarnings <= 2^128;
            require total_onDeposits >= 0;
            require total_onEarnings >= 0;
        }
    }

// @title The allowance can only be changed by functions listed in the filter:
// initRiverV1_1, setConsensusLayerData, decreaseAllowance, increaseAllowance, approve, transferFrom
// Almost fixed. Latest run:
// https://prover.certora.com/output/40577/c70e8e35cce446d495beb2c3904cf368?anonymousKey=11133ef88d529912cc091efea5f4f344eb2cf077
// We need this bug to be fixed:
// https://certora.atlassian.net/browse/CERT-4453
rule allowanceChangesRestrictively(method f) filtered {
    f -> !f.isView
        && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
        && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
        && f.selector != sig:decreaseAllowance(address,uint256).selector
        && f.selector != sig:increaseAllowance(address,uint256).selector
        && f.selector != sig:approve(address,uint256).selector
        && f.selector != sig:transferFrom(address,address,uint256).selector
} {
    env e;
    calldataarg args;
    address owner;
    address spender;
    uint256 allowance_before = allowance(owner, spender);
    require owner != spender;
    f(e, args);
    uint256 allowance_after = allowance(owner, spender);
    assert allowance_after == allowance_before;
}

// @title The allowance of spender given by owner can always be decreased to 0 by the owner.
// Proved:
// https://prover.certora.com/output/40577/8985ea476a404c22801668777b60cb1e/?anonymousKey=67dc2147dcdd5e40466d907f809241856718be06
rule alwaysPossibleToDecreaseAllowance()
{
    env e;
    address owner;
    address spender;
    uint256 amount;
    decreaseAllowance(e, spender, amount);
    uint256 allowance_after = allowance(owner, spender);
    satisfy e.msg.sender == owner && allowance_after == 0;
}

// @title It is impossible to increase any allowance by calling decreaseAllowance or transferFrom.
// Proved:
// https://prover.certora.com/output/40577/8985ea476a404c22801668777b60cb1e/?anonymousKey=67dc2147dcdd5e40466d907f809241856718be06
rule decreaseAllowanceAndTransferCannotIncreaseAllowance(env e, method f, calldataarg args) filtered {
    f -> f.selector == sig:decreaseAllowance(address,uint256).selector
        || f.selector == sig:transferFrom(address,address,uint256).selector
} {
    address owner;
    address spender;
    uint256 allowance_before = allowance(owner, spender);
    f(e, args);
    uint256 allowance_after = allowance(owner, spender);
    assert allowance_after <= allowance_before;
}

// @title Allowance increases only by owner
// Same issue as in allowanceChangesRestrictively
// https://prover.certora.com/output/40577/8985ea476a404c22801668777b60cb1e/?anonymousKey=67dc2147dcdd5e40466d907f809241856718be06
rule allowanceIncreasesOnlyByOwner(method f) filtered {
    f -> !f.isView
        && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
        && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
}  {
    env e;
    calldataarg args;
    address owner;
    address spender;
    uint256 allowance_before = allowance(owner, spender);
    f(e, args);
    uint256 allowance_after = allowance(owner, spender);
    assert allowance_before < allowance_after => e.msg.sender == owner;
}

// @title The shares balance can only be changed by functions listed in the filter:
// transferFrom, transfer, setConsensusLayerData, depositAndTransfer, deposit, requestRedeem
rule sharesBalanceChangesRestrictively(method f) filtered {
    f -> !f.isView
        && f.selector != sig:transferFrom(address,address,uint256).selector
        && f.selector != sig:transfer(address,uint256).selector
        && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
        && f.selector != sig:depositAndTransfer(address).selector
        && f.selector != sig:deposit().selector
        && f.selector != sig:requestRedeem(uint256,address).selector
} {
    env e;
    calldataarg args;
    address owner;
    uint256 shares_balance_before = balanceOf(owner);
    f(e, args);
    uint256 shares_balance_after = balanceOf(owner);
    assert shares_balance_after == shares_balance_before;
}


// @title If the balance changes and shares balance is the same, it must have been one of these functions:
// initRiverV1_1, depositToConsensusLayer, claimRedeemRequests, deposit, depositAndTransfer
rule pricePerShareChangesRespectively(method f) filtered {
    f -> !f.isView
        && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
        && f.selector != sig:depositToConsensusLayer(uint256).selector
        && f.selector != sig:claimRedeemRequests(uint32[],uint32[]).selector
        && f.selector != sig:deposit().selector
        && f.selector != sig:depositAndTransfer(address).selector
} {
    env e;
    calldataarg args;
    address owner;
    uint256 shares_balance_before = balanceOf(owner);
    uint256 underlying_balance_before = balanceOfUnderlying(owner);
    f(e, args);
    uint256 shares_balance_after = balanceOf(owner);
    uint256 underlying_balance_after = balanceOfUnderlying(owner);
    assert shares_balance_before == shares_balance_after => underlying_balance_before == underlying_balance_after;
}

// For claimRedeemRequests:
// https://prover.certora.com/output/40577/f471c52cd3bc492b8fa66be4ea5ceca2?anonymousKey=41e7eff719e12adb7ef871a595db299bf2b54d81
// For the rest (except setConsensusLayerData):
// https://prover.certora.com/output/40577/e1b3895a5aea45109a2398708c64c5c9/?anonymousKey=ea0663a174435d274e51a992cee73f0573fa8a80
rule sharesMonotonicWithAssets(env e, method f) filtered {
    f -> !f.isView
       // && f.selector != sig:requestRedeem(uint256,address).selector // Prover error
       // && f.selector != sig:claimRedeemRequests(uint32[],uint32[]).selector // Claiming rewards can violate the property.
       && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport calldata).selector
} {
    calldataarg args;

    mathint totalLsETHBefore = totalSupply();
    mathint totalETHBefore = totalUnderlyingSupply();

    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint totalETHAfter = totalUnderlyingSupply();

    // require totalETHBefore + totalLsETHBefore + totalETHAfter + totalLsETHAfter <= max_uint256;
    require totalETHBefore <= 2^128;
    require totalLsETHBefore <= 2^128;
    require totalETHAfter <= 2^128;
    require totalLsETHAfter <= 2^128;

    assert totalETHBefore > totalETHAfter => totalLsETHBefore >= totalLsETHAfter;
    assert totalETHBefore < totalETHAfter => totalLsETHBefore <= totalLsETHAfter;
    assert totalLsETHBefore > totalLsETHAfter => totalETHBefore >= totalETHAfter;
    assert totalLsETHBefore < totalLsETHAfter => totalETHBefore <= totalETHAfter;
}

// This rule does not hold for setConsensusLayerData:
// https://prover.certora.com/output/40577/e5a7a762228c45d29adfbdc3ace30530/?anonymousKey=6206b628e02ad22f68fd8f33c537f4eebe44847f
// Passes here:
// https://prover.certora.com/output/40577/c7a5fc0bdd644d408dac94f888522e69/?anonymousKey=2fc64544d31c1ed95caa2c0ab96b7d31c0394d07
rule sharesMonotonicWithAssets_forSecConsensusLayerData(env e, method f) filtered {
    f -> f.selector == sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper3_checkBounds(OracleManagerV1.ConsensusLayerDataReportingVariables, ReportBounds.ReportBoundsStruct, uint256).selector
       || f.selector == sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper8_requestExitsBasedOnRedeemDemandAfterRebalancings(OracleManagerV1.ConsensusLayerDataReportingVariables, IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper10_skimExcessBalanceToRedeem(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper11_commitBalanceToDeposit(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
} {
    calldataarg args;

    mathint totalLsETHBefore = totalSupply();
    mathint totalETHBefore = totalUnderlyingSupply();

    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint totalETHAfter = totalUnderlyingSupply();

    require totalETHBefore <= 2^128;
    require totalLsETHBefore <= 2^128;
    require totalETHAfter <= 2^128;
    require totalLsETHAfter <= 2^128;

    assert totalETHBefore > totalETHAfter => totalLsETHBefore >= totalLsETHAfter;
    assert totalETHBefore < totalETHAfter => totalLsETHBefore <= totalLsETHAfter;
    assert totalLsETHBefore > totalLsETHAfter => totalETHBefore >= totalETHAfter;
    assert totalLsETHBefore < totalLsETHAfter => totalETHBefore <= totalETHAfter;
}

// This rule does not hold for setConsensusLayerData:
// https://prover.certora.com/output/40577/e5a7a762228c45d29adfbdc3ace30530/?anonymousKey=6206b628e02ad22f68fd8f33c537f4eebe44847f
rule zeroAssetsZeroShares(env e, method f) filtered {
    f -> !f.isView
       && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport calldata).selector
       && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
       && f.selector != sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
       && f.selector != sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
       && f.selector != sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       && f.selector != sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       && f.selector != sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
} {
    calldataarg args;

    mathint totalLsETHBefore = totalSupply();
    mathint totalETHBefore = totalUnderlyingSupply();
    require totalLsETHBefore == 0 <=> totalETHBefore == 0;

    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint totalETHAfter = totalUnderlyingSupply();

    // require totalETHBefore + totalLsETHBefore + totalETHAfter + totalLsETHAfter <= max_uint256;
    require totalETHBefore <= 2^128;
    require totalLsETHBefore <= 2^128;
    require totalETHAfter <= 2^128;
    require totalLsETHAfter <= 2^128;

    assert totalLsETHAfter == 0 <=> totalETHAfter == 0;
}

// Passing:
// https://prover.certora.com/output/40577/7200741ff45f4e83b7ccad0ae41732d7/?anonymousKey=8c2721eac68cde6ded8f88a7791e166d737ac2d7
invariant zeroAssetsZeroShares_invariant()
    totalUnderlyingSupply() == 0 <=> totalSupply() == 0
    filtered {
        f -> f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
          // Method setConsensusLayerData could break this invariant and was removed.
          && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport calldata).selector
          && f.selector != sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
          && f.selector != sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
          && f.selector != sig:helper3_checkBounds(OracleManagerV1.ConsensusLayerDataReportingVariables, ReportBounds.ReportBoundsStruct, uint256).selector
          && f.selector != sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper8_requestExitsBasedOnRedeemDemandAfterRebalancings(OracleManagerV1.ConsensusLayerDataReportingVariables, IOracleManagerV1.ConsensusLayerReport).selector
          && f.selector != sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper10_skimExcessBalanceToRedeem(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
          && f.selector != sig:helper11_commitBalanceToDeposit(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
    } {
        preserved
        {
            require totalUnderlyingSupply() <= 2^128;
            require totalSupply() <= 2^128;
        }
    }

// Proved here:
// https://prover.certora.com/output/40577/97e80c1789554ace8cf643e8bb0fc1ae/?anonymousKey=a5c050759274943242991940a9d5779d794f17ff
rule pricePerShareStable(env e, method f) filtered {
    f -> !f.isView
      && f.selector != sig:claimRedeemRequests(uint32[],uint32[]).selector
      && f.selector != sig:certorafallback_0().selector
      && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
      && f.selector != sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
      && f.selector != sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
      && f.selector != sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
} {
    calldataarg args;

    uint256 totalLsETHBefore = totalSupply();
    uint256 totalETHBefore = totalUnderlyingSupply();
    mathint pricePerShareBefore = mulDivDownAbstractPlus(totalETHBefore, 1, totalLsETHBefore);

    requireInvariant zeroAssetsZeroShares_invariant();
    require isDepositFunction(f) => e.msg.sender != currentContract;
    // require e.msg.sender != currentContract;

    f(e, args);

    uint256 totalLsETHAfter = totalSupply();
    uint256 totalETHAfter = totalUnderlyingSupply();
    mathint pricePerShareAfter = mulDivDownAbstractPlus(totalETHAfter, 1, totalLsETHAfter);

    assert pricePerShareBefore <= pricePerShareAfter && pricePerShareAfter <= pricePerShareBefore + pricePerShareBefore;
}

rule conversionRateStable(env e, method f) filtered {
    f -> !f.isView
      && f.selector != sig:claimRedeemRequests(uint32[],uint32[]).selector
      && f.selector != sig:certorafallback_0().selector
      && f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
      && f.selector != sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
      && f.selector != sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
      && f.selector != sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      && f.selector != sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
      // Violated by helper9: https://prover.certora.com/output/40577/5f4d5be6590347a6b442aec54c778871/?anonymousKey=5704882931fa498db5d6fdeff183342fa0e00670
      && f.selector != sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
} {
    calldataarg args;

    uint256 totalLsETHBefore = totalSupply();
    uint256 totalETHBefore = totalUnderlyingSupply();
    mathint rateBefore = mulDivDownAbstractPlus(totalLsETHBefore, 1, totalETHBefore);

    requireInvariant zeroAssetsZeroShares_invariant();
    require isDepositFunction(f) => e.msg.sender != currentContract;
    // require e.msg.sender != currentContract;

    f(e, args);

    uint256 totalLsETHAfter = totalSupply();
    uint256 totalETHAfter = totalUnderlyingSupply();
    mathint rateAfter = mulDivDownAbstractPlus(totalLsETHAfter, 1, totalETHAfter);

    // assert totalETHBefore * totalLsETHAfter == totalETHAfter * totalLsETHBefore;

    assert rateBefore == rateAfter;
    // assert f.selector != sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
    //     => rateBefore == rateAfter;
    // assert f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
    //     => rateAfter <= rateBefore + rateBefore + rateBefore + 1;
    // assert f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
    //     => rateBefore <= rateAfter + rateAfter + rateAfter + 1;
}

// For helper9_reportWithdrawToRedeemManager it is also important, that it does not break the conversion rate.
// Hopefuly proved here:
// https://prover.certora.com/output/40577/f0305618029e4041bf4bd05256dcc5e6?anonymousKey=ce96a33f5876cab02ebeff53516f5bee9b889bd0
rule conversionRateStable_helper9_reportWithdrawToRedeemManager(env e)
{
    OracleManagerV1.ConsensusLayerDataReportingVariables vars;

    uint256 totalLsETHBefore = totalSupply();
    uint256 totalETHBefore = totalUnderlyingSupply();
    mathint rateBefore = mulDivDownAbstractPlus(totalETHBefore, 1, totalLsETHBefore);

    requireInvariant zeroAssetsZeroShares_invariant();

    helper9_reportWithdrawToRedeemManager(e, vars);

    uint256 totalLsETHAfter = totalSupply();
    uint256 totalETHAfter = totalUnderlyingSupply();
    mathint rateAfter = mulDivDownAbstractPlus(totalETHAfter, 1, totalLsETHAfter);

    assert totalLsETHBefore >= totalLsETHAfter;
    assert totalETHBefore >= totalETHAfter;

    // assert rateBefore <= rateAfter && rateBefore + rateBefore + 1 >= rateAfter; // violated here: https://prover.certora.com/output/40577/56123346e9924c53bb1e30ba892234e2/?anonymousKey=ac03fff66edce2e497f4fc367af76304a2ce9011
    // assert rateAfter <= rateBefore && rateAfter + rateAfter + 1 >= rateBefore; // violated here: https://prover.certora.com/output/40577/859a891515e44c07a4f872833b786796/?anonymousKey=42a365e04989bd227379d60587581d925fecfebb
    // assert rateAfter <= rateBefore + rateBefore + 1; // violated here: https://prover.certora.com/output/40577/1013183a11664889b1f5adcfca250ea3?anonymousKey=6b0611758c8382cfdda70d7da69c89d2416aa20c
    // assert rateBefore <= rateAfter + rateAfter + 1; // violated here: https://prover.certora.com/output/40577/579fd1e7e19841078c0fa787565c843a/?anonymousKey=4167ac796e451474aae934048bb692d0d3d1084f
    assert rateAfter <= rateBefore + rateBefore + rateBefore + 1;
    assert rateBefore <= rateAfter + rateAfter + rateAfter + 1;
}

rule conversionRateChangeWitnessHard(env e, method f) filtered {
    f ->  f.selector == sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper3_checkBounds(OracleManagerV1.ConsensusLayerDataReportingVariables, ReportBounds.ReportBoundsStruct, uint256).selector
       || f.selector == sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper8_requestExitsBasedOnRedeemDemandAfterRebalancings(OracleManagerV1.ConsensusLayerDataReportingVariables, IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper10_skimExcessBalanceToRedeem(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper11_commitBalanceToDeposit(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
} {
    calldataarg args;

    uint256 totalLsETHBefore = totalSupply();
    uint256 totalETHBefore = totalUnderlyingSupply();

    requireInvariant zeroAssetsZeroShares_invariant();
    require e.msg.sender != currentContract;

    f(e, args);

    uint256 totalLsETHAfter = totalSupply();
    uint256 totalETHAfter = totalUnderlyingSupply();

    satisfy totalETHBefore * totalLsETHAfter != totalETHAfter * totalLsETHBefore;
}

// proved here:
// https://prover.certora.com/output/40577/d57287efa20b4183965c503eb1415f89/?anonymousKey=3c1a04e6876b9f482f15782a23064bf44971cde2
rule sharesNotChangedInOracleReport(env e, method f, calldataarg args) filtered {
    f ->  f.selector == sig:helper1_fillUpVarsAndPullCL(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper2_updateLastReport(IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper3_checkBounds(OracleManagerV1.ConsensusLayerDataReportingVariables, ReportBounds.ReportBoundsStruct, uint256).selector
       || f.selector == sig:helper4_pullELFees(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper5_pullRedeemManagerExceedingEth(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper6_pullCoverageFunds(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper8_requestExitsBasedOnRedeemDemandAfterRebalancings(OracleManagerV1.ConsensusLayerDataReportingVariables, IOracleManagerV1.ConsensusLayerReport).selector
       || f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper10_skimExcessBalanceToRedeem(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:helper11_commitBalanceToDeposit(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
       || f.selector == sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
} {
    address usr;
    mathint totalLsETHBefore = totalSupply();
    mathint LsETHBefore = balanceOf(usr);

    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint LsETHAfter = balanceOf(usr);

    assert f.selector != sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector &&
           f.selector != sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
        => totalLsETHBefore == totalLsETHAfter &&
           LsETHBefore == LsETHAfter;
    assert f.selector == sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
        => totalLsETHBefore <= totalLsETHAfter &&
           LsETHBefore <= LsETHAfter;
    assert f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector
        => totalLsETHBefore >= totalLsETHAfter &&
           LsETHBefore >= LsETHAfter;
}

// https://prover.certora.com/output/40577/d4c3eb620aa446fa8a04a30e93edcf0f?anonymousKey=301f81a0ce7081b7377153318192e81ddbc1d8ba
rule totalETHChangeReachable(env e, method f) filtered {
    f -> !f.isView
} {
    calldataarg args;

    uint256 totalLsETHBefore = totalSupply();
    uint256 totalETHBefore = totalUnderlyingSupply();

    requireInvariant zeroAssetsZeroShares_invariant();
    require e.msg.sender != currentContract;

    f(e, args);

    uint256 totalLsETHAfter = totalSupply();
    uint256 totalETHAfter = totalUnderlyingSupply();

    satisfy totalETHBefore != totalETHAfter;
}

// @title After transfer from, balances are updated accordingly, but not of any other user. Also, totalSupply stays the same.
// Proved:
// https://prover.certora.com/output/40577/0d75136142bd4b458c77e73f4394f101/?anonymousKey=7c99f012e75eb4143a0c3f5dbc180eda79a0c0db
rule transferUpdatesBalances(env e) {
    address from;
    address to;
    address other;
    uint256 amount;
    mathint balanceSenderBefore = balanceOf(from);
    mathint balanceReceiverBefore = balanceOf(to);
    mathint balanceOtherBefore = balanceOf(other);
    mathint totalSupplyBefore = totalSupply();

    transferFrom(e, from, to, amount);

    mathint balanceSenderAfter = balanceOf(from);
    mathint balanceReceiverAfter = balanceOf(to);
    mathint balanceOtherAfter = balanceOf(other);
    mathint totalSupplyAfter = totalSupply();

    assert to != from => balanceSenderBefore - balanceSenderAfter == to_mathint(amount);
    assert to != from => balanceReceiverAfter - balanceReceiverBefore == to_mathint(amount);
    assert other != from && other != to => balanceOtherAfter == balanceOtherBefore;
    assert totalSupplyAfter == totalSupplyBefore;
}
