methods {
    function _.get_deposit_root() external => DISPATCHER(true);
    // getDepositData is summarized in specs/summaries/RiverV1_base_summaries.spec
    // (CVL function `getDepositDataSummary`) — see comment there for why we don't
    // dispatch into DepositDataBufferMock for this entry point.
    // function _.getDepositData(bytes32) external => DISPATCHER(true);

    function _.claimRedeemRequests(uint32[],uint32[],bool,uint16) external => DISPATCHER(true);
    function _.demandETHExits(uint256,uint256) external => DISPATCHER(true);
    function _.getAllowlist() external => DISPATCHER(true);
    function _.getExitedETHAndRequestedExitAmounts() external => DISPATCHER(true);
    function _.getKeeper() external => DISPATCHER(true);
    function _.getOperatorCount() external => DISPATCHER(true);
    function _.getRedeemDemand() external => DISPATCHER(true);
    function _.getSlashingContainmentMode() external => DISPATCHER(true);
    function _.incrementFundedETH(uint256[],bytes[][]) external => DISPATCHER(true);
    function _.isDenied(address) external => DISPATCHER(true);
    function _.onlyAllowed(address,uint256) external => DISPATCHER(true);
    function _.pullCoverageFunds(uint256) external => DISPATCHER(true);
    function _.pullELFees(uint256) external => DISPATCHER(true);
    function _.pullEth(uint256) external => DISPATCHER(true);
    function _.pullExceedingEth(uint256) external => DISPATCHER(true);
    function _.reportCLETH(uint256[]) external => DISPATCHER(true);
    function _.reportExitedETH(uint256[],uint256) external => DISPATCHER(true);
    function _.reportWithdraw(uint256) external => DISPATCHER(true);
    function _.requestRedeem(uint256,address,address) external => DISPATCHER(true);
    function _.resolveRedeemRequests(uint32[]) external => DISPATCHER(true);
    function _.sendCLFunds() external => DISPATCHER(true);
    function _.sendCoverageFunds() external => DISPATCHER(true);
    function _.sendELFees() external => DISPATCHER(true);
    function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    function _.sharesFromUnderlyingBalance(uint256) external => DISPATCHER(true);
    function _.transfer(address,uint256) external => DISPATCHER(true);
    function _.transferFrom(address,address,uint256) external => DISPATCHER(true);
    function _.underlyingBalanceFromShares(uint256) external => DISPATCHER(true);
}