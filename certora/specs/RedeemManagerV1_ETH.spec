import "RedeemManagerV1.spec";

using RiverMock as river;
use invariant HeightOfSubequentRequest;
use rule mulDivLIACheck;
use rule mulDivMonotonicCheck;

methods {
    function river.totalShares() external returns (uint256) envfree;
    function river.assetBalance() external returns (uint256) envfree;
    function river.sharesPerOwner(address) external returns (uint256) envfree;

    function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    function _.underlyingBalanceFromShares(uint256 _shares) external => DISPATCHER(true);
    function _.transferFrom(address _from, address _to, uint256 _value) external => DISPATCHER(true);
    function RiverMath.mulDiv(uint256 a, uint256 b, uint256 c) internal returns (uint256) => mulDivLIA(a, b, c);
}

definition min256(uint256 x, uint256 y) returns uint256 =  x < y ? x : y;

/// @title Any pushed event comes together with the event ETH deposit to the contract.
rule eventIsPushedTogetherWithETH() {
    env e; 
    /// River is sender, which is not the manager.
    require e.msg.sender != currentContract;
    uint256 lsETHWithdrawable;
    uint32 eventID = require_uint32(getWithdrawalEventCount());
    
    mathint balance_before = nativeBalances[currentContract];
        reportWithdraw(e, lsETHWithdrawable);
    mathint balance_after = nativeBalances[currentContract];

    assert balance_after - balance_before == to_mathint(getWithdrawalEventDetails(eventID).withdrawnEth);
}

/// @title It's impossible for any matching request to drain an event more than its withdrawn ETH.
rule cannotDrainMoreThanEventETH(uint32 eventID) {
    env e1;
    env e2;
    uint32 requestID1; 
    uint32 requestID2;
    requireInvariant HeightOfSubequentRequest(requestID1, requestID2);
    requireInvariant HeightOfSubequentRequest(requestID2, requestID1);

    mathint eventETH = getWithdrawalEventDetails(eventID).withdrawnEth;

    mathint managerETH_0 = nativeBalances[currentContract];
        claimRedeemRequests(e1, [requestID1], [eventID], true, 0);
    mathint managerETH_1 = nativeBalances[currentContract];

    assert managerETH_0 - managerETH_1 <= eventETH;
    
    mathint eventETHRemaining = eventETH - (managerETH_0 - managerETH_1);
        claimRedeemRequests(e2, [requestID2], [eventID], true, 0);
    mathint managerETH_2 = nativeBalances[currentContract];

    assert managerETH_1 - managerETH_2 <= eventETHRemaining;
}

/// @title The change in the contract ETH balance is equal to the change in the request max redeemable ETH.
rule changeOfContractEthBalanceIsChangeOfMatchingPair(uint32 requestID, uint32 eventID) {
    bool match = isMatchByID(requestID, eventID);

    uint256 requestETH_pre = getRedeemRequestDetails(requestID).maxRedeemableEth;
    mathint eventETH = getWithdrawalEventDetails(eventID).withdrawnEth;
    uint256 balanceManager_pre = nativeBalances[currentContract];
        env e;
        require e.msg.sender != currentContract;
        claimRedeemRequests(e, [requestID], [eventID], true, 0);
    uint256 balanceManager_post = nativeBalances[currentContract];
    uint256 requestETH_post = getRedeemRequestDetails(requestID).maxRedeemableEth;

    assert match => balanceManager_pre - balanceManager_post <= eventETH;
    assert match => balanceManager_pre - balanceManager_post == requestETH_pre - requestETH_post;
    /// The function should revert when there is no match, so the following assert vacuously holds.
    assert !match => balanceManager_post == balanceManager_pre;
}

/// @title the maximum amount of redeemed ETH is equal to maxRedeemableEth.
rule maxRedeemedAmount(uint32 ID) {
    env e;
    uint32[] withdrawalEvents;
    uint16 depth;
    RedeemQueue.RedeemRequest request = getRedeemRequestDetails(ID);

    mathint balanceRecipient_pre = nativeBalances[request.owner];
    mathint balanceManager_pre = nativeBalances[currentContract];
        claimRedeemRequests(e, [ID], withdrawalEvents, true, depth);
    mathint balanceRecipient_post = nativeBalances[request.owner];
    mathint balanceManager_post = nativeBalances[currentContract];

    mathint amountPaid = balanceManager_pre - balanceManager_post;
    assert amountPaid == balanceRecipient_post - balanceRecipient_pre;
    assert amountPaid <= to_mathint(request.maxRedeemableEth);
}

/// @title The request "share price" (= maxRedeemableEth/amount in request) cannot increase.
rule requestSharePriceCannotIncrease(uint32 requestID) {
    RedeemQueue.RedeemRequest request_pre = getRedeemRequestDetails(requestID);
    require request_pre.amount !=0;
    uint256 sharePrice_pre = mulDivLIA(request_pre.maxRedeemableEth, 10^18, request_pre.amount);
        env e;
        calldataarg args;
        claimRedeemRequests(e, args);
    RedeemQueue.RedeemRequest request_post = getRedeemRequestDetails(requestID);
    require request_post.amount !=0;
    uint256 sharePrice_post = mulDivLIA(request_post.maxRedeemableEth, 10^18, request_post.amount);

    assert to_mathint(sharePrice_post) <= sharePrice_pre + 1;
}

/// @title the share price of redeemed ETH is the minimum between the withdrawal event and request share prices.
rule minimalSharePrice(uint32 requestID, uint32 eventID) {
    env e;
    RedeemQueue.RedeemRequest request_pre = getRedeemRequestDetails(requestID);
    WithdrawalStack.WithdrawalEvent event = getWithdrawalEventDetails(eventID);
        claimRedeemRequests(e, [requestID], [eventID], true, 0);
    RedeemQueue.RedeemRequest request_post = getRedeemRequestDetails(requestID);
    
    uint256 deltaShares = assert_uint256(request_pre.amount - request_post.amount);
    uint256 deltaEth = assert_uint256(request_pre.maxRedeemableEth - request_post.maxRedeemableEth);
    /// Redeem share price is the minimum between event share price and request share price.
    uint256 ethFromRequest = mulDivLIA(request_pre.maxRedeemableEth, deltaShares, request_pre.amount);
    uint256 ethFromEvent = mulDivLIA(event.withdrawnEth, deltaShares, event.amount);

    assert deltaEth <= min256(ethFromEvent, ethFromRequest);
    assert to_mathint(deltaEth) >= min256(ethFromEvent, ethFromRequest) - 1;
}

/// @title the redeem manager cannot send shares back.
rule redeemManagerDoesntSendShares(method f) filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    uint256 shares_before = river.sharesPerOwner(currentContract);
    f(e,args);
    uint256 shares_after = river.sharesPerOwner(currentContract);
    
    assert shares_after >= shares_before;
}
