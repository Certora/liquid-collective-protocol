import "Sanity.spec";
import "MathSummaries.spec";
import "Base.spec";


use rule method_reachability;

// sanity passes here:
// https://prover.certora.com/output/40577/2031abdd92254bafb49b487cb7466b12?anonymousKey=cef84e43b9a622eb29ce44539dba2dd9a9721096
// sanity with less unresolved calls here:
// https://prover.certora.com/output/40577/49c466500a5248b8b95e9a3a6a2ea245?anonymousKey=e1f4c6e3f2bc651eccad0ed1463ece870525478b


methods {
    // MathSummarizations
    function _.mulDivDown(uint256 a, uint256 b, uint256 c) internal => mulDivDownAbstractPlus(a, b, c) expect uint256 ALL;
}


// @title Checks basic formula: totalSupply of shares must match number of underlying tokens.
// Proved
// https://prover.certora.com/output/40577/a451e923be1144ae88f125ac4f7b7a60?anonymousKey=69814a5c38c0f7720859be747546bbbde3f79191
invariant totalSupplyBasicIntegrity()
    totalSupply() == sharesFromUnderlyingBalance(totalUnderlyingSupply());

// @title setConsensusLayerData does not break the following statement: river balance is equal to the sum BalanceToDeposit.get() + CommittedBalance.get() + BalanceToRedeem.get()
// https://prover.certora.com/output/40577/70efd3b673224aebae46ced21e150dce/?anonymousKey=68b4b3fa514f4aceb895c1306f3b44c48e2b4773
rule riverBalanceIsSumOf_ToDeposit_Commmitted_ToRedeem_for_setConsensusLayerData(env e)
{
    mathint assets_before = totalUnderlyingSupply();
    uint256 toDeposit_before = getBalanceToDeposit();
    uint256 committed_before = getCommittedBalance();
    uint256 toRedeem_before = getBalanceToRedeem();
    require assets_before == toDeposit_before + committed_before + toRedeem_before;

    IOracleManagerV1.ConsensusLayerReport report;

    setConsensusLayerData(e, report);

    mathint assets_after = totalUnderlyingSupply();
    uint256 toDeposit_after = getBalanceToDeposit();
    uint256 committed_after = getCommittedBalance();
    uint256 toRedeem_after = getBalanceToRedeem();

    assert assets_after == toDeposit_after + committed_after + toRedeem_after;
}

rule memoryVarsCanBeModifiedFromWithinFunction(env e)
{
    OracleManagerV1.ConsensusLayerDataReportingVariables vars;
    uint256 a;
    require a == vars.trace.rewards;
    helper4_pullELFees(e, vars);
    satisfy vars.trace.rewards != a;
}

rule riverBalanceIsSumOf_ToDeposit_Commmitted_ToRedeem_for_helper2_helper7(env e)
{
    mathint assets_before = totalUnderlyingSupply();
    uint256 toDeposit_before = getBalanceToDeposit();
    uint256 committed_before = getCommittedBalance();
    uint256 toRedeem_before = getBalanceToRedeem();
    mathint sum_before = toDeposit_before + committed_before + toRedeem_before;
    uint256 river_balance_before = riverEthBalance();
    require e.msg.sender != currentContract;

    IOracleManagerV1.ConsensusLayerReport report;
    OracleManagerV1.ConsensusLayerDataReportingVariables vars1 = helper1_fillUpVarsAndPullCL(e, report);

    helper2_updateLastReport(e, report); // Just reports, no changes to argument.

    uint256 totalSupplyMidterm = totalUnderlyingSupply();
    uint256 val_balance_midterm = report.validatorsBalance;

    OracleManagerV1.ConsensusLayerDataReportingVariables vars4 = helper4_pullELFees(e, vars1);

    helper7_onEarnings(e, vars4); // Just pull on earnings, no changes to argument

    mathint assets_after = totalUnderlyingSupply();
    uint256 toDeposit_after = getBalanceToDeposit();
    uint256 committed_after = getCommittedBalance();
    uint256 toRedeem_after = getBalanceToRedeem();
    mathint sum_after = toDeposit_after + committed_after + toRedeem_after;
    uint256 river_balance_after = riverEthBalance();

    assert river_balance_after + sum_before == sum_after + river_balance_before;
}

// Passing except for timeout for claimRedeemRequests:
// https://prover.certora.com/output/40577/03d0c8799cd7442e8c50ecfee4c940cc/?anonymousKey=110f1e2ba0710a7ee8312516d636e201b73d3576
rule riverBalanceIsSumOf_ToDeposit_Commmitted_ToRedeem(env e, method f, calldataarg args) filtered {
    f -> !f.isView
        && f.selector != sig:sendCoverageFunds().selector
        && f.selector != sig:sendCLFunds().selector
        && f.selector != sig:sendRedeemManagerExceedingFunds().selector
        && f.selector != sig:certorafallback_0().selector
        && f.selector != sig:sendELFees().selector
} {
    mathint assets_before = totalUnderlyingSupply();
    uint256 toDeposit_before = getBalanceToDeposit();
    uint256 committed_before = getCommittedBalance();
    uint256 toRedeem_before = getBalanceToRedeem();
    mathint sum_before = toDeposit_before + committed_before + toRedeem_before;
    uint256 river_balance_before = riverEthBalance();

    uint256 totalSupplyMidterm = totalUnderlyingSupply();
    require e.msg.sender != currentContract;

    f(e, args);

    mathint assets_after = totalUnderlyingSupply();
    uint256 toDeposit_after = getBalanceToDeposit();
    uint256 committed_after = getCommittedBalance();
    uint256 toRedeem_after = getBalanceToRedeem();
    mathint sum_after = toDeposit_after + committed_after + toRedeem_after;
    uint256 river_balance_after = riverEthBalance();

    assert river_balance_after + sum_before == sum_after + river_balance_before;
}

invariant riverBalanceIsSumOf_ToDeposit_Commmitted_ToRedeem_invariant()
    to_mathint(totalUnderlyingSupply()) == getBalanceToDeposit() + getCommittedBalance() + getBalanceToRedeem()
    filtered {
        f -> f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector
        && f.selector != sig:setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector
    }

rule underlyingBalanceEqualToRiverBalancePlusConsensus_claimRedeemRequests(env e)
{
    require getDepositedValidatorCount() <= getCLValidatorCount();
    require getCLValidatorCount() <= 2^64;
    require consensusLayerDepositSize() <= 2^64;
    require to_mathint(totalUnderlyingSupply()) == riverEthBalance() + consensusLayerEthBalance();

    uint32[] _redeemRequestIds;
    uint32[] _withdrawalEventIds;

    claimRedeemRequests(e, _redeemRequestIds, _withdrawalEventIds);

    assert to_mathint(totalUnderlyingSupply()) == riverEthBalance() + consensusLayerEthBalance();
}

rule consensusLayerEth_changeVitness(env e, method f, calldataarg args)
{
    mathint consensusLayerBalanceBefore = consensusLayerEthBalance();

    f(e, args);

    mathint consensusLayerBalanceAfter = consensusLayerEthBalance();

    assert consensusLayerBalanceBefore == consensusLayerBalanceAfter; // To see which function can change this
}

rule consensusLayerDepositSize_changeVitness(env e, method f, calldataarg args)
{
    mathint depositSizeBefore = consensusLayerDepositSize();

    f(e, args);

    mathint depositSizeAfter = consensusLayerDepositSize();

    assert depositSizeAfter == 2;
//    satisfy depositSizeBefore != depositSizeAfter; // To see which function can change this
}

rule getCLValidatorTotalBalance_changeVitness(env e, env e2, method f, calldataarg args)
{
    mathint before = getCLValidatorTotalBalance(e2);

    f(e, args);

    mathint after = getCLValidatorTotalBalance(e2);

    satisfy before != after; // To see which function can change this
}

rule getLastConsensusLayerReport_changeVitness(env e, env e2, method f, calldataarg args)
{
    IOracleManagerV1.StoredConsensusLayerReport before = getLastConsensusLayerReport(e2);

    f(e, args);

    IOracleManagerV1.StoredConsensusLayerReport after = getLastConsensusLayerReport(e2);

    assert before.epoch == after.epoch; // To see which function can change this
    assert after.epoch == 0;
}

rule underlyingBalanceEqualToRiverBalancePlusConsensus(env e, method f, calldataarg args)
{
    require to_mathint(totalUnderlyingSupply()) == riverEthBalance() + consensusLayerEthBalance();

    f(e, args);

    assert to_mathint(totalUnderlyingSupply()) == riverEthBalance() + consensusLayerEthBalance();
}

// // Validators will exit the consensus layer.
// // Naively, they exits with the initial 32 ETH.
// // number of validators exitting x initial DEPOSIT_SIZE  <<< 
// rule validatorsExitRequestsCorrectness(env e)
// {
//     OracleManagerV1.ConsensusLayerDataReportingVariables vars;
//     IOracleManagerV1.ConsensusLayerReport report;
//     helper8_requestExitsBasedOnRedeemDemandAfterRebalancings(e, vars, report);
//     assert false;
// }

// @title When user deposits, there is no additional gift component to the deposit.
// Passing here:
// https://prover.certora.com/output/40577/ab8a00d9e5804d6eb56316149457cbf8/?anonymousKey=224f9317520c66cc0c214cb632a02918577a85ef
rule depositAdditivityNoGiftsToEachDeposit(env e1, env e2, env eSum) {
    mathint amount1;
    mathint amount2;
    address recipient;

    require amount1 == to_mathint(e1.msg.value);
    require amount2 == to_mathint(e2.msg.value);
    require amount1 + amount2 == to_mathint(eSum.msg.value);

    mathint sharesBefore = balanceOf(recipient);

    storage initial = lastStorage;

    depositAndTransfer(e1, recipient);
    mathint shares1 = balanceOf(recipient);

    depositAndTransfer(e2, recipient) at initial;
    mathint shares2 = balanceOf(recipient);

    depositAndTransfer(eSum, recipient) at initial;
    mathint sharesSum = balanceOf(recipient);

    assert shares1 + shares2 <= sharesSum + sharesBefore;
}
