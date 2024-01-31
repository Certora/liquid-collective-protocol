import "Base.spec";

methods {
    // WLSETH
    function WLSETHV1.totalSupply() external returns(uint256) envfree;
    function WLSETHV1.balanceOf(address) external returns(uint256) envfree;

    // // AllowlistV1
    // function AllowlistV1.onlyAllowed(address, uint256) external envfree;
    // function _.onlyAllowed(address, uint256) external => DISPATCHER(true);
    // function AllowlistV1.isDenied(address) external returns (bool) envfree;
    // function _.isDenied(address) external => DISPATCHER(true);

    // // RedeemManagerV1
    // function RedeemManagerV1Harness.resolveRedeemRequests(uint32[]) external returns(int64[]) envfree;
    // function _.resolveRedeemRequests(uint32[]) external => DISPATCHER(true);
    //  // requestRedeem function is also defined in River:
    // // function _.requestRedeem(uint256) external => DISPATCHER(true); //not required, todo: remove
    // function _.requestRedeem(uint256 _lsETHAmount, address _recipient) external => DISPATCHER(true);
    // function _.claimRedeemRequests(uint32[], uint32[], bool, uint16) external => DISPATCHER(true);
    // // function _.claimRedeemRequests(uint32[], uint32[]) external => DISPATCHER(true); //not required, todo: remove
    // function _.pullExceedingEth(uint256) external => DISPATCHER(true);
    // function _.reportWithdraw(uint256) external => DISPATCHER(true);
    // function RedeemManagerV1Harness.getRedeemDemand() external returns (uint256) envfree;
    // function _.getRedeemDemand() external => DISPATCHER(true);

    // // RiverV1
    // function RiverV1Harness.getBalanceToDeposit() external returns(uint256) envfree;
    // function RiverV1Harness.getCommittedBalance() external returns(uint256) envfree;
    // function RiverV1Harness.getBalanceToRedeem() external returns(uint256) envfree;
    // function RiverV1Harness.consensusLayerDepositSize() external returns(uint256) envfree;
    // function RiverV1Harness.riverEthBalance() external returns(uint256) envfree;
    // function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    // function _.getAllowlist() external => DISPATCHER(true);
    // function RiverV1Harness.getAllowlist() external returns(address) envfree;
    // function _.sendCLFunds() external => DISPATCHER(true);
    // function _.sendCoverageFunds() external => DISPATCHER(true);
    // function _.sendELFees() external => DISPATCHER(true);

    // // RiverV1 : SharesManagerV1
    // function _.transferFrom(address, address, uint256) external => DISPATCHER(true);
    // function _.underlyingBalanceFromShares(uint256) external => DISPATCHER(true);
    // function RiverV1Harness.underlyingBalanceFromShares(uint256) external returns(uint256) envfree;
    // function RiverV1Harness.balanceOfUnderlying(address) external returns(uint256) envfree;
    // function RiverV1Harness.totalSupply() external returns(uint256) envfree;
    // function RiverV1Harness.totalUnderlyingSupply() external returns(uint256) envfree;
    // function RiverV1Harness.sharesFromUnderlyingBalance(uint256) external returns(uint256) envfree;
    // function RiverV1Harness.balanceOf(address) external returns(uint256) envfree;
    // function RiverV1Harness.consensusLayerEthBalance() external returns(uint256) envfree;
    // // RiverV1 : OracleManagerV1
    // function _.setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport) external => DISPATCHER(true);
    // function RiverV1Harness.getCLValidatorCount() external returns(uint256) envfree;
    // // RiverV1 : ConsensusLayerDepositManagerV1
    // function _.depositToConsensusLayer(uint256) external => DISPATCHER(true);
    // function RiverV1Harness.getDepositedValidatorCount() external returns(uint256) envfree;

    // // WithdrawV1
    // function _.pullEth(uint256) external => DISPATCHER(true);

    // // ELFeeRecipientV1
    // function _.pullELFees(uint256) external => DISPATCHER(true);

    // // CoverageFundV1
    // function _.pullCoverageFunds(uint256) external => DISPATCHER(true);

    // // OperatorsRegistryV1
    // function _.reportStoppedValidatorCounts(uint32[], uint256) external => DISPATCHER(true);
    // //function OperatorsRegistryV1.getStoppedAndRequestedExitCounts() external returns (uint32, uint256) envfree;
    // function _.getStoppedAndRequestedExitCounts() external => DISPATCHER(true);
    // function _.demandValidatorExits(uint256, uint256) external => DISPATCHER(true);
    // function _.pickNextValidatorsToDeposit(uint256) external => DISPATCHER(true); // has no effect - CERT-4615

    // function _.deposit(bytes,bytes,bytes,bytes32) external => DISPATCHER(true); // has no effect - CERT-4615

    // // function _.increment_onDepositCounter() external => ghostUpdate_onDepositCounter() expect bool ALL;

    // // MathSummarizations
    // // function _.mulDivDown(uint256 a, uint256 b, uint256 c) internal => mulDivDownAbstractPlus(a, b, c) expect uint256 ALL;

    // //workaroun per CERT-4615
    // function LibBytes.slice(bytes memory _bytes, uint256 _start, uint256 _length) internal returns (bytes memory) => bytesSliceSummary(_bytes, _start, _length);
}

// function returnRiver()
// ghost mathint total_onDeposits{ // counter checking number of calls to _onDeposit
//     init_state axiom total_onDeposits == 0;// this is total earned ETH
// }

// function returnRiver() returns 
// {
//     counter_onEarnings = counter_onEarnings + 1;
//     total_onEarnings = total_onEarnings + amount;
//     return true;
// }

invariant balanceOfLessOrEqualTotalSupply(env e, address usr)
    totalSupply() >= balanceOf(usr);

