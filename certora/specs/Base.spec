using AllowlistV1 as AL;
using CoverageFundV1 as CF;
using ELFeeRecipientV1 as ELFR;
using OperatorsRegistryV1 as OR;
using RedeemManagerV1Harness as RM;
using WithdrawV1 as Wd;

methods {
    // AllowlistV1
    function AllowlistV1.onlyAllowed(address, uint256) external envfree;
    function _.onlyAllowed(address, uint256) external => DISPATCHER(true);
    function AllowlistV1.isDenied(address) external returns (bool) envfree;
    function _.isDenied(address) external => DISPATCHER(true);

    // RedeemManagerV1
    function RedeemManagerV1Harness.resolveRedeemRequests(uint32[]) external returns(int64[]) envfree;
    function _.resolveRedeemRequests(uint32[]) external => DISPATCHER(true);
    function _.requestRedeem(uint256 _lsETHAmount, address _recipient) external => DISPATCHER(true);
    function _.claimRedeemRequests(uint32[], uint32[], bool, uint16) external => DISPATCHER(true);
    function _.pullExceedingEth(uint256) external => DISPATCHER(true);
    function _.reportWithdraw(uint256) external => DISPATCHER(true);
    function RedeemManagerV1Harness.getRedeemDemand() external returns (uint256) envfree;
    function _.getRedeemDemand() external => DISPATCHER(true);

    // RiverV1

    function getBalanceToDeposit() external returns(uint256) envfree;
    function getCommittedBalance() external returns(uint256) envfree;
    function getBalanceToRedeem() external returns(uint256) envfree;
    function consensusLayerDepositSize() external returns(uint256) envfree;
    function riverEthBalance() external returns(uint256) envfree;
    function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    function _.getAllowlist() external => DISPATCHER(true);
    function RiverV1Harness.getAllowlist() external returns(address) envfree;
    function _.sendCLFunds() external => DISPATCHER(true);
    function _.sendCoverageFunds() external => DISPATCHER(true);
    function _.sendELFees() external => DISPATCHER(true);

    // RiverV1 : SharesManagerV1
    function _.transferFrom(address, address, uint256) external => DISPATCHER(true);
    function _.underlyingBalanceFromShares(uint256) external => DISPATCHER(true);
    function RiverV1Harness.underlyingBalanceFromShares(uint256) external returns(uint256) envfree;
    function RiverV1Harness.balanceOfUnderlying(address) external returns(uint256) envfree;
    function RiverV1Harness.totalSupply() external returns(uint256) envfree;
    function RiverV1Harness.totalUnderlyingSupply() external returns(uint256) envfree;
    function RiverV1Harness.sharesFromUnderlyingBalance(uint256) external returns(uint256) envfree;
    function RiverV1Harness.balanceOf(address) external returns(uint256) envfree;
    function RiverV1Harness.consensusLayerEthBalance() external returns(uint256) envfree;
    // RiverV1 : OracleManagerV1
    function _.setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport) external => DISPATCHER(true);
    function RiverV1Harness.getCLValidatorCount() external returns(uint256) envfree;
    // RiverV1 : ConsensusLayerDepositManagerV1
    function _.depositToConsensusLayer(uint256) external => DISPATCHER(true);
    function RiverV1Harness.getDepositedValidatorCount() external returns(uint256) envfree;

    // WithdrawV1
    function _.pullEth(uint256) external => DISPATCHER(true);

    // ELFeeRecipientV1
    function _.pullELFees(uint256) external => DISPATCHER(true);

    // CoverageFundV1
    function _.pullCoverageFunds(uint256) external => DISPATCHER(true);

    // OperatorsRegistryV1
    function _.reportStoppedValidatorCounts(uint32[], uint256) external => DISPATCHER(true);
    function OperatorsRegistryV1.getStoppedAndRequestedExitCounts() external returns (uint32, uint256) envfree;
    function _.getStoppedAndRequestedExitCounts() external => DISPATCHER(true);
    function _.demandValidatorExits(uint256, uint256) external => DISPATCHER(true);
    function _.pickNextValidatorsToDeposit(uint256) external => DISPATCHER(true); // has no effect - CERT-4615

    function _.deposit(bytes,bytes,bytes,bytes32) external => DISPATCHER(true); // has no effect - CERT-4615

    function LibBytes.slice(bytes memory _bytes, uint256 _start, uint256 _length) internal returns (bytes memory) => bytesSliceSummary(_bytes, _start, _length);
}

function bytesSliceSummary(bytes buffer, uint256 start, uint256 len) returns bytes {
	bytes to_ret;
	return to_ret;
}
