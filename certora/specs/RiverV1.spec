import "Sanity.spec";
import "MathSummaries.spec";
import "RiverBase.spec";

use rule method_reachability;
use rule mulDivValueDelta;
use rule mulDivLIACheck;
use rule mulDivMonotonicCheck;
use rule mulDivAdditivity;
use rule mulDivBurnSharePriceDelta_underlying;
use rule mulDivBurnSharePriceDelta_shares;

methods {
    function math.mulDiv(uint256 a, uint256 b, uint256 c) internal returns (uint256) => mulDivLIA(a, b, c);
}

/// @title Checks basic formula: totalSupply of shares must match number of underlying tokens.
/// Proven
invariant totalSupplyBasicIntegrity()
    totalSupply() == sharesFromUnderlyingBalance(totalUnderlyingSupply());

/// @title The shares total supply is zero iff the underlying ETH supply is zero.
invariant zeroAssetsZeroShares_invariant()
    totalUnderlyingSupply() == 0 <=> totalSupply() == 0
    filtered {f -> !helperMethods(f)}

/// @title The River ETH balance covers the validators balance + balance to deposit + committed balance + balance to redeem.
invariant riverBalancePlusConsensusCoversUnderlyingSupply()
    to_mathint(totalUnderlyingSupply()) <= riverEthBalance() + consensusLayerEthBalance()
filtered{f -> !helperMethods(f) && !claimRedeemMethod(f) && !setConsensusMethod(f)}
{
    preserved with (env e) {
        require e.msg.sender != currentContract;
    }
    /// Simplification: assuming only one key at a time.
    /// Proven for any maxCount (<= 3):
    /// https://prover.certora.com/output/41958/b2cd145cbe5b4ea68f0a60ea6c3deb4b/?anonymousKey=24351898af9ae329019cc5d9c2c0557f0bc667b1
    preserved depositToConsensusLayer(uint256 _maxCount) with (env e) {
        require e.msg.sender != currentContract;
        require _maxCount == 1;
    }
}

rule riverBalancePlusConsensusCoversUnderlyingSupply_setConsensus() {
    require to_mathint(totalUnderlyingSupply()) <= riverEthBalance() + consensusLayerEthBalance();

    env e;
    require e.msg.sender != currentContract;
    calldataarg args;
    setConsensusLayerData(e, args);

    assert to_mathint(totalUnderlyingSupply()) <= riverEthBalance() + consensusLayerEthBalance();
}

rule riverBalancePlusConsensusCoversUnderlyingSupply_claimRedeem() {
    require to_mathint(totalUnderlyingSupply()) <= riverEthBalance() + consensusLayerEthBalance();

    env e;
    require e.msg.sender != currentContract;
    calldataarg args;
    claimRedeemRequests(e, args);

    assert to_mathint(totalUnderlyingSupply()) <= riverEthBalance() + consensusLayerEthBalance();
}

/// @title depositToConsensusLayer is associative with respect to the number of keys.
/*rule depositToConsensusLayerAssociative() {
    env e;
    storage initState = lastStorage;
    depositToConsensusLayer(e, 1) at initState;
    depositToConsensusLayer(e, 1);

    uint256 riverBalanceA = riverEthBalance();
    uint256 underlyingSupplyA = totalUnderlyingSupply();

    depositToConsensusLayer(e, 2) at initState;

    uint256 riverBalanceB = riverEthBalance();
    uint256 underlyingSupplyB = totalUnderlyingSupply();

    assert riverBalanceA == riverBalanceB && underlyingSupplyA == underlyingSupplyB;
}*/

/// @title Share price stability after burning shares
/// @notice - can fail if burning all shares but some ETH remains in the underlying supply.
rule sharePriceMaxDecrease_reportWithdraw() 
{
    requireInvariant zeroAssetsZeroShares_invariant();
    SetSuppliesBounds();
    env e;
    calldataarg args;
    require e.msg.sender != currentContract;
    uint256 supplyBefore = totalSupply();
    uint256 underlyingBefore = totalUnderlyingSupply(); 
    uint256 balanceToRedeem = getBalanceToRedeem();
    uint256 redeemDemand = RM.getRedeemDemand();
    burnSharePriceDelta_underlying(balanceToRedeem, supplyBefore, underlyingBefore);
    burnSharePriceDelta_shares(redeemDemand, supplyBefore, underlyingBefore);

    mathint rateBefore = getSharePrice();
        helper9_reportWithdrawToRedeemManager(e, args);
    mathint rateAfter = getSharePrice();
    uint256 balanceAfter = totalUnderlyingSupply();

    assert (balanceAfter !=0 && rateAfter !=0) => rateBefore - rateAfter <= min(rateBefore, max(2, (rateBefore * rateBefore) /  balanceAfter + 1));
}

/// @title When a user deposits, there is no additional gift component to the deposit.
/// Proven:
/// https://prover.certora.com/output/41958/587584c193fa4941ae1ee3b93babd240/?anonymousKey=d58d2abe2a4b1c37d8dfac67d3fcac94249e38d8
rule noGiftsInDeposit(env e) {
    address recipient;
    address sender = e.msg.sender;
    require e.msg.sender != currentContract;
    uint256 supplyBefore = totalSupply();
    uint256 underlyingBefore = totalUnderlyingSupply(); 

    SetSuppliesBounds();
    requireInvariant zeroAssetsZeroShares_invariant();
    mintedSharesValueDelta(e.msg.value, balanceOf(recipient), supplyBefore, underlyingBefore);
    /// Remains to be proven
    require recipient != sender => balanceOf(sender) + balanceOf(recipient) <= to_mathint(supplyBefore);
    require sender == recipient => balanceOf(sender) <= supplyBefore;

    mathint senderValue_before = getUserValue(e.msg.sender);
    mathint recipientValue_before = getUserValue(recipient);
        depositAndTransfer(e, recipient);
    mathint senderValue_after = getUserValue(e.msg.sender);
    mathint recipientValue_after = getUserValue(recipient);

    mathint rounding_error = underlyingBefore != 0 ? 1 + underlyingBefore / supplyBefore : 0;
    uint256 delta = recipient == sender ? 0 : e.msg.value;

     if(recipient != currentContract) {
        assert recipientValue_after - recipientValue_before <= delta + 1;
        assert recipientValue_after - recipientValue_before >= delta - rounding_error;
    }
    else {
    /// If the recipient is the current contract, the delta should account for the deposit value (e.msg.value)
    /// so delta -> delta + msg.value = 2*delta
        assert recipientValue_after - recipientValue_before <= 2*delta + 1;
        assert recipientValue_after - recipientValue_before >= 2*delta - rounding_error;
    }
}

/// @title Given a lower bound on the epochs per frame, there is only one valid epoch at every timestamp.
invariant OnlyOneValidEpoch(env e, uint256 epoch1, uint256 epoch2)
    getCurrentEpochId(e) - getLastCompletedEpochId(e) < getCLSpec(e).epochsPerFrame + getCLSpec(e).epochsToAssumedFinality
    =>
    (epoch1 != epoch2 => !(isValidEpoch(e, epoch1) && isValidEpoch(e, epoch2)))
    filtered{f -> !setConsensusMethod(f)}
