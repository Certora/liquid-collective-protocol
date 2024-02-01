import "MathSummaries.spec";

methods {
    function getRedeemRequestDetails(uint32) external returns (RedeemQueue.RedeemRequest) envfree;
    function resolveRedeemRequests(uint32[]) external returns (int64[]) envfree;

    function getRedeemRequestCount() external returns (uint256) envfree;
    function getWithdrawalEventCount() external returns (uint256) envfree;
    function getWithdrawalEventDetails(uint32) external returns (WithdrawalStack.WithdrawalEvent) envfree;
    
    /// CLAIM status
    function CLAIM_FULLY_CLAIMED() external returns (uint8) envfree;
    function CLAIM_PARTIALLY_CLAIMED() external returns (uint8) envfree;
    function CLAIM_SKIPPED() external returns (uint8) envfree;

    /// Harness:
    function getWithdrawalEventHeight(uint32 id) external returns (uint256) envfree;  
    function getWithdrawalEventAmount(uint32 id) external returns (uint256) envfree;   
    function getRedeemRequestHeight(uint32 id) external returns (uint256) envfree;    
    function getRedeemRequestAmount(uint32 id) external returns (uint256) envfree;
    function isMatchByID(uint32 requestID, uint32 eventID) external returns (bool) envfree;

    //function RedeemManagerV1._performDichotomicResolution(RedeemQueue.RedeemRequest memory request) internal returns (int64) => dichotomicResolution(request);
}

/// Summary for _performDichotomicResolution
function dichotomicResolution(RedeemQueue.RedeemRequest request) returns int64 {
    int64 count = require_int64(getWithdrawalEventCount() - 1);
    int64 index; require index >=0 && index <= count;
    return index;
}

/// @title The owner of any redeem request is not the zero address.
invariant NonZeroRedeemRequestOwner(uint32 requestId)
    to_mathint(requestId) < to_mathint(getRedeemRequestCount()) => getRedeemRequestDetails(requestId).owner != 0; 

/// @title The height of the first withdrawal event is zero.
invariant HeightOfFirstEventIsZero()
    getWithdrawalEventHeight(0) == 0
    {
        preserved {require getWithdrawalEventCount() < max_uint32;}
    }

/// @title The Height difference of two adjacent withdrawal events is the amount of the former.
invariant WithdrawalEventsHeightDifferenceIsAmount(uint32 ID)
    ID + 1 < to_mathint(getWithdrawalEventCount()) =>
    getWithdrawalEventHeight(ID) + getWithdrawalEventAmount(ID) ==
    to_mathint(getWithdrawalEventHeight(require_uint32(ID+1)))
    {
        preserved {require getWithdrawalEventCount() < max_uint32;}
    }

/// @title If any two requests match the same withdrawal event, then their height difference must be smaller than the event size.
rule twoRequestsMatchTheSameEvent(uint32 requestID1, uint32 requestID2) {
    uint32 eventID;
    require requestID1 < requestID2;
    require eventID < require_uint32(getWithdrawalEventCount());
    requireInvariant HeightOfSubequentRequest(requestID1, requestID2);
    requireInvariant HeightOfSubequentRequest(requestID2, requestID1);

    uint256 height1 = getRedeemRequestHeight(requestID1);
    uint256 height2 = getRedeemRequestHeight(requestID2);
    mathint amountEvent = getWithdrawalEventAmount(eventID);

    assert isMatchByID(requestID1, eventID) && isMatchByID(requestID2, eventID) =>
        height2 - height1 <= amountEvent;
}

/// @title If any two events match the same redeem request, then their height difference must be smaller than the request size.
rule twoEventsMatchTheSameRequest(uint32 eventID1, uint32 eventID2) {
    uint32 requestID;
    require eventID1 < eventID2;
    require requestID < require_uint32(getWithdrawalEventCount());
    requireInvariant HeightOfSubequentEvent(eventID1, eventID2);
    requireInvariant HeightOfSubequentEvent(eventID2, eventID1);

    uint256 height1 = getWithdrawalEventHeight(eventID1);
    uint256 height2 = getWithdrawalEventHeight(eventID2);
    mathint amountRequest = getRedeemRequestAmount(requestID);

    assert isMatchByID(requestID, eventID1) && isMatchByID(requestID, eventID2) =>
        height2 - height1 <= amountRequest;
}

/// @title Any registered withdrawal event has non-zero amount.
/// @notice: violated - River doesn't restrict zero shares events.
invariant WithdrawalEventHasNonZeroAmount(uint32 eventID)
    assert_uint256(eventID) < getWithdrawalEventCount() => getWithdrawalEventAmount(eventID) !=0
    {
        preserved reportWithdraw(uint256 lsETHWithdrawable) with (env e) {
            /// Not guaranteed!
            /// Must be verified in the River.
            // require lsETHWithdrawable !=0;
        }
        preserved {
            require getWithdrawalEventCount() < max_uint32;
        }
    } 

/// @title The height of the first redeem request, right after creation, is zero.
rule firstRedeemRequestHeightIsZero() {
    uint256 redeemRequestCount = getRedeemRequestCount();
    env e; 
    uint256 lsETHAmount; address recipient;
    uint32 redeemRequestId = requestRedeem(e, lsETHAmount, recipient);
    uint256 requestHeight = getRedeemRequestHeight(redeemRequestId);

    assert redeemRequestId == redeemRequestId;
    assert redeemRequestCount == 0 => requestHeight == 0;
}

/// @title For every redeem request, the sum of its height and shares amount is preserved once created.
rule sumOfRequestHeightAndAmountIsPreserved(uint32 requestID, method f) filtered{f -> !f.isView} {
    env e;
    calldataarg args;
    uint256 requestsCount = getRedeemRequestCount();
    require requestsCount < max_uint32;
    mathint sumBefore = getRedeemRequestAmount(requestID) + getRedeemRequestHeight(requestID);
        f(e, args);
    mathint sumAfter = getRedeemRequestAmount(requestID) + getRedeemRequestHeight(requestID);

    assert assert_uint256(requestID) < requestsCount => sumBefore == sumAfter;
}

/// @title The redeem requests array cannot drop requests - length doesn't decrease.
rule redeemRequestsNeverDrop(method f) filtered{f -> !f.isView} {

    uint256 numberOfRequests_before = getRedeemRequestCount();
    require numberOfRequests_before < max_uint32;
        env e;
        calldataarg args;
        f(e, args);
    uint256 numberOfRequests_after = getRedeemRequestCount();

    assert numberOfRequests_before <= numberOfRequests_after;
    assert numberOfRequests_after - numberOfRequests_before == 1 || numberOfRequests_before == numberOfRequests_after;
}

/// @title The redeem amount of any request cannot increase()
rule redeemRequestAmountCannotIncrease(uint32 requestID, method f) filtered{f -> !f.isView} {
    
    uint32 requestsCount = require_uint32(getRedeemRequestCount());
    require requestsCount < max_uint32;
    uint256 amount_before = getRedeemRequestAmount(requestID);
        env e;
        calldataarg args;
        f(e, args);
    uint256 amount_after = getRedeemRequestAmount(requestID);

    assert requestID < requestsCount => amount_before >= amount_after;
}

/// @title The height of any redeem request is at least the sum of any of its previous request amount and height. 
/// Verified
invariant HeightOfSubequentRequest(uint32 requestID1, uint32 requestID2)
    (requestID1 < requestID2 && assert_uint256(requestID2) < getRedeemRequestCount()) 
        => getRedeemRequestAmount(requestID1) + getRedeemRequestHeight(requestID1) <= to_mathint(getRedeemRequestHeight(requestID2))
    {
        preserved {
            uint256 Nrequests = getRedeemRequestCount();
            uint32 lastRequestID = Nrequests == 0 ? 0 : require_uint32(Nrequests - 1);
            requireInvariant HeightOfSubequentRequest(requestID1, lastRequestID);
            requireInvariant HeightOfSubequentRequest(requestID2, lastRequestID);
            require getRedeemRequestCount() < max_uint32;
        }
    }

/// @title The height of any withdrawal event is at least the sum of any of its previous event amount and height. 
/// Verified
invariant HeightOfSubequentEvent(uint32 eventID1, uint32 eventID2)
    (eventID1 < eventID2 && assert_uint256(eventID2) < getWithdrawalEventCount())
        => getWithdrawalEventAmount(eventID1) + getWithdrawalEventHeight(eventID1) <= to_mathint(getWithdrawalEventHeight(eventID2))
    {
        preserved {
            uint256 Nevents = getWithdrawalEventCount();
            uint32 lastEventID = Nevents == 0 ? 0 : require_uint32(Nevents - 1); 
            requireInvariant HeightOfSubequentEvent(eventID1, lastEventID);
            requireInvariant HeightOfSubequentEvent(eventID2, lastEventID);
            require getRedeemRequestCount() < max_uint32;
            require Nevents < max_uint32;
        }
    }

/// @title No previous claim request can change the amount redeemd by another request.
rule subequentRequestCannotStealClaim(uint32 ID1, uint32 ID2) {
    env e;
    /// First request
    uint32[] redeemRequestIds1 = [ID1];
    uint32[] withdrawalEventIds1;
    uint16 depth1;
    /// Second request
    uint32[] redeemRequestIds2 = [ID2];
    uint32[] withdrawalEventIds2; 
    uint16 depth2;

    requireInvariant HeightOfSubequentRequest(ID1, ID2);
    requireInvariant HeightOfSubequentRequest(ID2, ID1);
    requireInvariant HeightOfSubequentEvent(withdrawalEventIds1[0], withdrawalEventIds2[0]);
    requireInvariant HeightOfSubequentEvent(withdrawalEventIds2[0], withdrawalEventIds1[0]);
    require getRedeemRequestCount() < max_uint32;

    storage initState = lastStorage;
    claimRedeemRequests(e, redeemRequestIds1, withdrawalEventIds1, true, depth1) at initState;
    uint256 amountPostA = getRedeemRequestAmount(ID1);

    claimRedeemRequests(e, redeemRequestIds2, withdrawalEventIds2, true, depth2) at initState;
    claimRedeemRequests(e, redeemRequestIds1, withdrawalEventIds1, true, depth1);
    uint256 amountPostB = getRedeemRequestAmount(ID1);

    assert ID2 != ID1 => amountPostA == amountPostB;
}

/// @title The claimRedeemRequest() function is depth-associative (for each request separately).
rule claimRequestDepthAssociative(uint32 ID) {
    env e;
    uint32 eventID;
    uint32 nextEvent = require_uint32(eventID);
    storage initState = lastStorage;

    claimRedeemRequests(e, [ID], [eventID], true, 0) at initState;
    claimRedeemRequests(e, [ID], [nextEvent], true, 0);
    RedeemQueue.RedeemRequest requestPostA = getRedeemRequestDetails(ID);

    claimRedeemRequests(e, [ID], [eventID], true, 1) at initState;
    RedeemQueue.RedeemRequest requestPostB = getRedeemRequestDetails(ID);

    assert ( 
        requestPostA.amount == requestPostB.amount &&
        requestPostA.maxRedeemableEth == requestPostB.maxRedeemableEth &&
        requestPostA.height == requestPostB.height &&
        requestPostA.owner == requestPostB.owner
    );
}

/// @title The claimRedeemRequest() function is amount-additive (for each request separately).
rule claimRequestAdditive(uint32 ID) {
    env e;
    uint32 withdrawalEventID1;
    uint32 withdrawalEventID2;
    uint16 depth;
    /// Split into two parts (same request)
    uint32[] redeemRequestIds1 = [ID];
    uint32[] withdrawalEventIds1 = [withdrawalEventID1];
    uint32[] redeemRequestIds2 = [ID];
    uint32[] withdrawalEventIds2 = [withdrawalEventID2];
    /// Case with two identical requests
    uint32[] redeemRequestIds3 = [ID, ID];
    uint32[] withdrawalEventIds3 = [withdrawalEventID1, withdrawalEventID2];
 
    storage initState = lastStorage;
    claimRedeemRequests(e, redeemRequestIds1, withdrawalEventIds1, true, depth) at initState;
    claimRedeemRequests@withrevert(e, redeemRequestIds2, withdrawalEventIds2, true, depth);
    bool reverted2 = lastReverted;
    uint256 amountPostA = getRedeemRequestAmount(ID);

    claimRedeemRequests@withrevert(e, redeemRequestIds3, withdrawalEventIds3, true, depth) at initState;
    bool reverted3 = lastReverted;
    uint256 amountPostB = getRedeemRequestAmount(ID);
    assert (!reverted2 && !reverted3) => amountPostA == amountPostB;
    assert reverted2 <=> reverted3;
}

/// @title claimRedeemRequests() is request-commutative.
rule claimRequestCommutative1(uint32 ID1, uint32 ID2) {
    env e;
    uint32 eventID1;
    uint32 eventID2;
    uint16 depth;
    /// Split into two parts (same request)
    uint32[] redeemRequestIdsA = [ID1, ID2];
    uint32[] withdrawalEventsIdsA = [eventID1, eventID2];
    uint32[] redeemRequestIdsB = [ID2, ID1];
    uint32[] withdrawalEventsIdsB = [eventID2, eventID1];
    requireInvariant HeightOfSubequentRequest(ID1, ID2);
    requireInvariant HeightOfSubequentRequest(ID2, ID1);
    requireInvariant HeightOfSubequentEvent(eventID1, eventID2);
    requireInvariant HeightOfSubequentEvent(eventID2, eventID1);
 
    storage initState = lastStorage;

    claimRedeemRequests(e, redeemRequestIdsA, withdrawalEventsIdsA, true, depth) at initState;
    RedeemQueue.RedeemRequest requestPostA = getRedeemRequestDetails(ID1);

    claimRedeemRequests(e, redeemRequestIdsB, withdrawalEventsIdsA, true, depth) at initState;
    RedeemQueue.RedeemRequest requestPostB = getRedeemRequestDetails(ID1);

    assert requestPostA.amount == requestPostB.amount;
    assert requestPostA.height == requestPostB.height;
    assert requestPostA.maxRedeemableEth == requestPostB.maxRedeemableEth;
}

/// @title claimRedeemRequests() is event-commutative.
rule claimRequestCommutative2(uint32 ID1, uint32 ID2) {
    env e;
    uint32 requestID1;
    uint32 requestID2;
    uint16 depth;
    /// Split into two parts (same request)
    uint32[] withdrawalEventsIdsA = [ID1, ID2];
    uint32[] redeemRequestIdsA = [requestID1, requestID2];
    uint32[] withdrawalEventsIdsB = [ID2, ID1];
    uint32[] redeemRequestIdsB = [requestID2, requestID1];
    requireInvariant HeightOfSubequentEvent(ID1, ID2);
    requireInvariant HeightOfSubequentEvent(ID2, ID1);
    requireInvariant HeightOfSubequentRequest(requestID1, requestID2);
    requireInvariant HeightOfSubequentRequest(requestID2, requestID1);
 
    storage initState = lastStorage;

    claimRedeemRequests(e, redeemRequestIdsA, withdrawalEventsIdsA, true, depth) at initState;
    RedeemQueue.RedeemRequest requestPostA = getRedeemRequestDetails(ID1);

    claimRedeemRequests(e, redeemRequestIdsA, withdrawalEventsIdsB, true, depth) at initState;
    RedeemQueue.RedeemRequest requestPostB = getRedeemRequestDetails(ID1);

    assert requestPostA.amount == requestPostB.amount;
    assert requestPostA.height == requestPostB.height;
    assert requestPostA.maxRedeemableEth == requestPostB.maxRedeemableEth;
}

// Given 2 consequent redeem requests and a single withdrawal event,
// if the second request is fully claimed then the first request cannot be partially claimed.
rule singleEventMustSatisfyEarlierRequestFirst(uint32 eventID) {
    uint32 requestID1; require requestID1 < require_uint32(getRedeemRequestCount());
    uint32 requestID2; require requestID2 < require_uint32(getRedeemRequestCount());
    requireInvariant HeightOfSubequentRequest(requestID1, requestID2);
    requireInvariant HeightOfSubequentRequest(requestID2, requestID1);

    env e;
    uint32[] redeemRequestIds = [requestID1, requestID2];
    uint32[] withdrawalEventIds = [eventID, eventID];
    bool skipAlreadyClaimed; 
    uint16 depth;

    uint8[] claimStatuses = 
        claimRedeemRequests(e, redeemRequestIds, withdrawalEventIds, skipAlreadyClaimed, depth);
    uint8 status1 = claimStatuses[0];
    uint8 status2 = claimStatuses[1];

    assert requestID1 < requestID2 => 
        status2 == CLAIM_FULLY_CLAIMED() => status1 != CLAIM_PARTIALLY_CLAIMED();
}

/// @title The output length of claimStatuses equals the length of redeem requests.
rule claimStatusesSizeEqualsRequestsSize() {
    env e;
    uint32[] redeemRequestIds; 
    uint32[] withdrawalEventIds; 
    bool skipAlreadyClaimed; 
    uint16 depth;

    uint8[] claimStatuses = 
        claimRedeemRequests(e, redeemRequestIds, withdrawalEventIds, skipAlreadyClaimed, depth);

    assert redeemRequestIds.length == claimStatuses.length;
}

/// @title The terminal (immutable) state of any redeem request is when its amount is zero.
rule fullClaimIsTerminal(uint32 requestID, method f) filtered { f-> !f.isView } {
    env e;
    RedeemQueue.RedeemRequest redeemRequest_pre = getRedeemRequestDetails(requestID);
    
    mathint redeemRequestCount = getRedeemRequestCount();
    require redeemRequestCount < max_uint32;
    /// Require that the request already exists (otherwise can turn from zero to non-zero)
    require to_mathint(requestID) < redeemRequestCount;
        calldataarg args;
        f(e, args);
    RedeemQueue.RedeemRequest redeemRequest_post = getRedeemRequestDetails(requestID);

    assert redeemRequest_pre.amount == 0 => (
        redeemRequest_pre.amount == redeemRequest_post.amount &&
        redeemRequest_pre.maxRedeemableEth == redeemRequest_post.maxRedeemableEth &&
        redeemRequest_pre.height == redeemRequest_post.height &&
        redeemRequest_pre.owner == redeemRequest_post.owner
    );
}

/// @title Request Ids are incremental, hence unique.
rule incrementalRedeemRequestId(method f) filtered { f-> !f.isView} {
    env e1;
    uint256 lsETHAmount1; address recipient1;
    uint32 redeemRequestId1 = requestRedeem(e1, lsETHAmount1, recipient1);
    require redeemRequestId1 < max_uint32;
    
    env e2; 
    calldataarg args;
    f(e2, args);
    
    env e3;
    uint256 lsETHAmount3; address recipient3;
    uint32 redeemRequestId3 = requestRedeem(e3, lsETHAmount3, recipient3);
    assert (f.selector != sig:requestRedeem(uint256,address).selector
           && f.selector != sig:requestRedeem(uint256).selector)
                => to_mathint(redeemRequestId3) == to_mathint(redeemRequestId1) + 1;
}

/// @title If the total height of an event is larger than the total height of a request,
/// then this event must fully satisfy this redeem request.
rule withdrawalHeightSatisfiesRequestLowerHeight() {
    env e;
    uint32 eventID; uint32[] withdrawalEventIds = [eventID];
    uint32 requestID; uint32[] redeemRequestIds = [requestID];
    bool skipAlreadyClaimed = true;
    uint16 depth;
    RedeemQueue.RedeemRequest redeemRequest = getRedeemRequestDetails(requestID);
    WithdrawalStack.WithdrawalEvent withdrawalEvent = getWithdrawalEventDetails(eventID);
    /// Assume request is not yet claimed.
    require redeemRequest.amount > 0;

    uint8[] claimStatuses = 
        claimRedeemRequests(e, redeemRequestIds, withdrawalEventIds, skipAlreadyClaimed, depth);

    assert (withdrawalEvent.height + withdrawalEvent.amount >= redeemRequest.height + redeemRequest.amount) => claimStatuses[0] == CLAIM_FULLY_CLAIMED();
}

/// @title Cannot drain a withdrawal event more than its size.
rule maximumDrainOfWithdrawalEvent() {
    env e1;
    env e2;
    uint32 eventID; uint32[] withdrawalEventIds = [eventID];
    uint32 requestID1; uint32[] redeemRequestIds1 = [requestID1];
    uint32 requestID2; uint32[] redeemRequestIds2 = [requestID2];
    requireInvariant HeightOfSubequentRequest(requestID1, requestID2);
    requireInvariant HeightOfSubequentRequest(requestID2, requestID1);

    bool skipAlreadyClaimed = true;
    uint16 depth = 0; /// Assume no recursion, so only the specific event is considered.
    mathint eventSize = getWithdrawalEventAmount(eventID);

    mathint amount1_before = getRedeemRequestAmount(requestID1);
        claimRedeemRequests(e1, redeemRequestIds1, withdrawalEventIds, skipAlreadyClaimed, depth);
    mathint amount1_after = getRedeemRequestAmount(requestID1);

    assert amount1_before - amount1_after <= eventSize;
    mathint eventAmountRemaining = eventSize - (amount1_before - amount1_after);

    mathint amount2_before = getRedeemRequestAmount(requestID2);
        claimRedeemRequests(e2, redeemRequestIds2, withdrawalEventIds, skipAlreadyClaimed, depth);
    mathint amount2_after = getRedeemRequestAmount(requestID2);

    assert amount2_before - amount2_after <= eventAmountRemaining;
}

/// @title Only a larger event amount can fully satisfy a request than is otherwise partially satisfied.
rule cannotFullyClaimForASmallerAmount(uint32 requestID) {
    env e;
    uint32 eventID1;
    uint32 eventID2;
    /// First event scenario 
    uint32[] redeemRequestIds1 = [requestID];
    uint32[] withdrawalEventIds1 = [eventID1];
    uint256 event1_amount = getWithdrawalEventAmount(eventID1);
    /// Second event scenario
    uint32[] redeemRequestIds2 = [requestID];
    uint32[] withdrawalEventIds2 = [eventID2];
    uint256 event2_amount = getWithdrawalEventAmount(eventID2);

    requireInvariant HeightOfSubequentEvent(eventID2, eventID1);
    requireInvariant HeightOfSubequentEvent(eventID1, eventID2);
    requireInvariant HeightOfSubequentEvent(eventID2, require_uint32(eventID2 + 1));
    
    bool skipAlreadyClaimed = true;
    uint16 depth = 0;
    storage initState = lastStorage;

    uint8[] claimStatuses1 = 
        claimRedeemRequests(e, redeemRequestIds1, withdrawalEventIds1, skipAlreadyClaimed, depth) at initState;

    uint8[] claimStatuses2 = 
        claimRedeemRequests(e, redeemRequestIds2, withdrawalEventIds2, skipAlreadyClaimed, depth) at initState;

    /// If the event amount is smaller than in a case where the request is partially satisfied, then 
    /// the second event must also be partially satisfied.
    assert (event1_amount > event2_amount && claimStatuses1[0] == CLAIM_PARTIALLY_CLAIMED()) =>
        claimStatuses2[0] == CLAIM_PARTIALLY_CLAIMED();
}

/// @title The claimed amount is monotonically increasing with the event size.
rule claimedAmountIsMonotonicWithEventSize(uint32 requestID) {
    env e;
    uint32 eventID1;
    uint32 eventID2;
    require eventID1 < eventID2;
    /// First event scenario 
    uint32[] redeemRequestIds1 = [requestID];
    uint32[] withdrawalEventIds1 = [eventID1];
    uint256 event1_amount = getWithdrawalEventAmount(eventID1);
    /// Second event scenario
    uint32[] redeemRequestIds2 = [requestID];
    uint32[] withdrawalEventIds2 = [eventID2];
    uint256 event2_amount = getWithdrawalEventAmount(eventID2);

    requireInvariant HeightOfSubequentEvent(eventID2, eventID1);
    requireInvariant HeightOfSubequentEvent(eventID1, eventID2);
    requireInvariant HeightOfSubequentEvent(eventID2, require_uint32(eventID2 + 1));
    requireInvariant HeightOfSubequentEvent(eventID1, require_uint32(eventID1 + 1));
    
    bool skipAlreadyClaimed = true;
    uint16 depth;
    storage initState = lastStorage;

    claimRedeemRequests(e, redeemRequestIds1, withdrawalEventIds1, skipAlreadyClaimed, depth) at initState;
    uint256 amountA = getRedeemRequestAmount(requestID);

    claimRedeemRequests(e, redeemRequestIds2, withdrawalEventIds2, skipAlreadyClaimed, depth) at initState;
    uint256 amountB = getRedeemRequestAmount(requestID);

    assert event1_amount > event2_amount => amountA <= amountB;
    assert amountA == amountB <=> amountA == 0;
}

rule satisfyRecursion(uint32 requestID, uint32 eventID) {
    env e;
    bool skipAlreadyClaimed = true;
    storage initState = lastStorage;

    claimRedeemRequests(e, [requestID], [eventID], skipAlreadyClaimed, 1) at initState;
    uint256 amountA = getRedeemRequestAmount(requestID);

    claimRedeemRequests(e, [requestID], [eventID], skipAlreadyClaimed, 2) at initState;
    uint256 amountB = getRedeemRequestAmount(requestID);

    satisfy amountA != amountB;
}

/// @title The resolveRedeemRequests() is requests-associative.
rule resolutionRequestsAssociative(uint32 ID1, uint32 ID2) {
    int64[] resolutions1 = resolveRedeemRequests([ID1]);
    int64[] resolutions2 = resolveRedeemRequests([ID2]);
    int64[] resolutions3 = resolveRedeemRequests([ID1, ID2]);

    assert resolutions1[0] == resolutions3[0];
    assert resolutions2[0] == resolutions3[1];
}

/// @title The resolution of resolveRedeemRequests() is always a match for the request.
rule resolutionRequestsYieldsAMatch(uint32 requestID) {
    require getWithdrawalEventCount() <= max_uint32;
    requireInvariant HeightOfFirstEventIsZero();

    int64[] resolutions = resolveRedeemRequests([requestID]);
    /// Assume a resolution has been found.
    uint32 eventID = require_uint32(resolutions[0]);

    assert isMatchByID(requestID, eventID); 
}
