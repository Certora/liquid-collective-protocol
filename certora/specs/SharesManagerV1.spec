import "RiverBase.spec";
import "MathSummaries.spec";

methods {
    function allowance(address, address) external returns(uint256) envfree;
    function balanceOf(address) external returns(uint256) envfree;
    function balanceOfUnderlying(address) external returns(uint256) envfree;
    function totalSupply() external returns(uint256) envfree;
    function math.mulDiv(uint256 a, uint256 b, uint256 c) internal returns (uint256) => mulDivDownAbstractPlus(a, b, c);
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
// https://prover.certora.com/output/41958/243b61d7e5e7421fb317450e25721fc6/?anonymousKey=1a99312c9a62add8fe74ced189162612f8c9158e
rule alwaysPossibleToDecreaseAllowance()
{
    env e;
    address owner = e.msg.sender;
    address spender;
    require e.msg.value == 0;
    require owner !=0 && spender !=0 ;
    decreaseAllowance@withrevert(e, spender, allowance(owner, spender));
    assert !lastReverted;
    assert allowance(owner, spender) == 0;
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
rule sharesMonotonicWithAssets(method f) filtered {f -> !f.isView && !setConsensusMethod(f)} {
    SetSuppliesBounds();

    mathint totalLsETHBefore = totalSupply();
    mathint totalETHBefore = totalUnderlyingSupply();
    env e;
    calldataarg args;
    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint totalETHAfter = totalUnderlyingSupply();
    
    assert totalETHBefore > totalETHAfter => totalLsETHBefore >= totalLsETHAfter;
    assert totalETHBefore < totalETHAfter => totalLsETHBefore <= totalLsETHAfter;
    assert totalLsETHBefore > totalLsETHAfter => totalETHBefore >= totalETHAfter;
    assert totalLsETHBefore < totalLsETHAfter => totalETHBefore <= totalETHAfter;
}

// This rule does not hold for setConsensusLayerData:
// https://prover.certora.com/output/40577/e5a7a762228c45d29adfbdc3ace30530/?anonymousKey=6206b628e02ad22f68fd8f33c537f4eebe44847f
// Passes here:
// https://prover.certora.com/output/40577/c7a5fc0bdd644d408dac94f888522e69/?anonymousKey=2fc64544d31c1ed95caa2c0ab96b7d31c0394d07
rule sharesMonotonicWithAssets_forSecConsensusLayerData(method f) filtered {f -> setConsensusMethod(f) } {
    env e;
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

// Violated for initRiverV1_1:
/// https://prover.certora.com/output/41958/3e6fedc6018d4887ac9371d35fbb2c24/?anonymousKey=f2750f9542e1e1990d48092eb1fe539c5e9a98ef
invariant zeroAssetsZeroShares_invariant()
    totalUnderlyingSupply() == 0 <=> totalSupply() == 0
    filtered {f -> !helperMethods(f)}
    //    f -> f.selector != sig:initRiverV1_1(address,uint64,uint64,uint64,uint64,uint64,uint256,uint256,uint128,uint128).selector 
    {
        preserved
        {
            SetSuppliesBounds();
        }
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

// proved here:
// https://prover.certora.com/output/40577/d57287efa20b4183965c503eb1415f89/?anonymousKey=3c1a04e6876b9f482f15782a23064bf44971cde2
rule sharesNotChangedInOracleReport(address user, method f) filtered {f -> helperMethods(f)} {
    mathint totalLsETHBefore = totalSupply();
    mathint LsETHBefore = balanceOf(user);
    
    env e;
    calldataarg args;
    f(e, args);

    mathint totalLsETHAfter = totalSupply();
    mathint LsETHAfter = balanceOf(user);

    bool is_onEarnings = f.selector == sig:helper7_onEarnings(OracleManagerV1.ConsensusLayerDataReportingVariables).selector;
    bool is_reportWithdraw = f.selector == sig:helper9_reportWithdrawToRedeemManager(OracleManagerV1.ConsensusLayerDataReportingVariables).selector;

    assert !(is_onEarnings || is_reportWithdraw) => (totalLsETHBefore == totalLsETHAfter && LsETHBefore == LsETHAfter);
    
    assert is_onEarnings => (totalLsETHBefore <= totalLsETHAfter && LsETHBefore <= LsETHAfter);
    
    assert is_reportWithdraw => (totalLsETHBefore >= totalLsETHAfter && LsETHBefore >= LsETHAfter);
}

/// @title Correctness of transferFrom(): 
/// a. balances are updated accordingly
/// b. Balances other than recipient and sender's are untouched.
/// c. totalSupply() is conserved.
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

/// @title It is never benefitial for any user to deposit in multiple smaller patches instead of one big patch.
rule depositSplittingIsNotProfitable(address recipient) {
    env e1;
    env e2;
    env e3;

    sharesAdditivityBound(e1.msg.value, e2.msg.value, totalSupply(), totalUnderlyingSupply());
    require e1.msg.value + e2.msg.value == to_mathint(e3.msg.value);

    storage initial = lastStorage;

    depositAndTransfer(e1, recipient) at initial;
    depositAndTransfer(e2, recipient);
    mathint sharesA = balanceOf(recipient);

    depositAndTransfer(e3, recipient) at initial;
    mathint sharesB = balanceOf(recipient);

    assert sharesA - sharesB <= 2;
}

/*
Rounding-down analysis shows that:
Given:
initial underlying supply (ETH) - X,
initial total supply (lsETH) - S,
Redeeming ds shares in exchange of dx (< X) ETH = sharesFromBalance(dx),
which results in (X , S) -> (X - dx , S - ds)  
leads to a change in (theoretical) share price that is bounded below by:

0 >= [ (X / S) _new / (X / S)_old ] - 1 >= - (X - 1) / S / (X - dx)
*/

rule sharePriceIsStable_revised(method f) filtered{f -> !f.isView && !helperMethods(f)} {
    requireInvariant zeroAssetsZeroShares_invariant();
    SetSuppliesBounds();
    env e;
    calldataarg args;
    require e.msg.sender != currentContract;

    mathint rateBefore = mulDivDownAbstractPlus(totalUnderlyingSupply(), 1, totalSupply());
        f(e, args);
    mathint rateAfter = mulDivDownAbstractPlus(totalUnderlyingSupply(), 1, totalSupply());

    assert abs(rateBefore - rateAfter) <= 2;
}

/// @title For every action that transfers shares, the sum of balances and total supply must not change.
rule totalSupplyAndSumOfBalancesArePreserved(address userA, address userB, method f) filtered{f -> 
    f.selector == sig:transfer(address,uint256).selector ||
    f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:requestRedeem(uint256,address).selector} 
{
    env e;
    uint256 amount;
    uint256 balanceA_before = balanceOf(userA);
    uint256 balanceB_before = balanceOf(userB);
    uint256 supply_before = totalSupply();

    if(f.selector == sig:transfer(address,uint256).selector) {
        require userA == e.msg.sender;
        transfer(e, userB, amount);
    }
    else if(f.selector == sig:transferFrom(address,address,uint256).selector) {
        transferFrom(e, userA, userB, amount);
    }
    else {
        address recipient;
        require userA == e.msg.sender;
        require userB == RM;
        requestRedeem(e, amount, recipient);
    }

    uint256 balanceA_after = balanceOf(userA);
    uint256 balanceB_after = balanceOf(userB);
    uint256 supply_after = totalSupply();

    assert balanceA_after + balanceB_after == balanceA_before + balanceB_before;
    assert supply_before == supply_after;
}

/// @title The share balance of any user is never larger than the total supply.
/// @notice Essentially, it's necessary to assume that the sum of all balances is smaller than the total supply.
invariant BalanceIsLessThanSupply(address user)
    balanceOf(user) <= totalSupply()
    filtered{f -> !setConsensusMethod(f)}
    {
        preserved transfer(address to, uint256 amount) with (env e) {
            require to != e.msg.sender => balanceOf(to) + balanceOf(e.msg.sender) <= to_mathint(totalSupply());
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e) {
            require to != from => balanceOf(to) + balanceOf(from) <= to_mathint(totalSupply());
        }
        preserved requestRedeem(uint256 amount, address to) with (env e) {
            require e.msg.sender != RM => balanceOf(e.msg.sender) + balanceOf(RM) <= to_mathint(totalSupply());
        }
        preserved with (env e) {
            require user != e.msg.sender => balanceOf(e.msg.sender) + balanceOf(user) <= to_mathint(totalSupply());
            require user != RM => balanceOf(RM) + balanceOf(user) <= to_mathint(totalSupply());
            require user != currentContract => balanceOf(currentContract) + balanceOf(user) <= to_mathint(totalSupply());
            require e.msg.sender != RM => balanceOf(e.msg.sender) + balanceOf(RM) <= to_mathint(totalSupply());
        }
    }
    
/// @title Shares transfer doesn't increase assets value
rule transferDoesntIncreaseValue(address userA, address userB, method f) filtered{f -> 
    f.selector == sig:transfer(address,uint256).selector ||
    f.selector == sig:transferFrom(address,address,uint256).selector ||
    f.selector == sig:requestRedeem(uint256,address).selector} 
{
    env e;
    calldataarg arg;
    
    mathint valueA_before = getUserValue(userA);
    mathint valueB_before = getUserValue(userB);

    uint256 amount;
    if(f.selector == sig:transfer(address,uint256).selector) {
        require userA == e.msg.sender;
        transfer(e, userB, amount);
    }
    else if(f.selector == sig:transferFrom(address,address,uint256).selector) {
        transferFrom(e, userA, userB, amount);
    }
    else {
        address recipient;
        require userA == e.msg.sender;
        require userB == RM;
        requestRedeem(e, amount, recipient);
    }

    mathint valueA_after = getUserValue(userA);
    mathint valueB_after = getUserValue(userB);

    assert valueA_after + valueB_after <= valueA_before + valueB_before + 1;
}

/// @title A user cannot increase the value of his own assets.
rule userCannotIncreaseOwnAssetsValue(method f) filtered{f -> !f.isView && !helperMethods(f) &&
/// claimRedeemRequests always gives value "for free" for the recipient.
f.selector != sig:claimRedeemRequests(uint32[],uint32[]).selector &&
/// Allowance breaks this property. We prove instead that the total value is preserved in another rule.
f.selector != sig:transferFrom(address,address,uint256).selector} 
{
    env e;
    address user = e.msg.sender;

    requireInvariant zeroAssetsZeroShares_invariant();
    requireInvariant BalanceIsLessThanSupply(user);
    require userIsNotAContract(user);
    SetSuppliesBounds();
    
    mathint value_before = getUserValue(user);
        calldataarg args;
        f(e, args);
    mathint value_after = getUserValue(user);

    assert value_after - value_before <= 1;
}

/// @title The assets of a black-listed user are immutable.
rule blackListedUserAssetsValueIsConstant(address user, method f) filtered{f -> !f.isView && !setConsensusMethod(f)} {
    require userIsNotAContract(user);
    require AL.isDenied(user); 

    SetSuppliesBounds();

    uint256 eth_before = nativeBalances[user];
    uint256 shares_before = balanceOf(user);
        env e;
        calldataarg args;
        f(e, args);
    uint256 eth_after = nativeBalances[user];
    uint256 shares_after = balanceOf(user);
    
    assert eth_after == eth_before && shares_after == shares_before;
}
