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