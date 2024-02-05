import "Sanity.spec";
import "CVLMath.spec";

using AllowlistV1 as AL;
using CoverageFundV1 as CF;
// using DepositContractMock as DCM;
using ELFeeRecipientV1 as ELFR;
// using OperatorsRegistryV1 as OR;
using RedeemManagerV1Harness as RM;
using WithdrawV1 as Wd;
using RiverV1Harness as RH;

use rule method_reachability;

methods {
    // AllowlistV1
    function AllowlistV1.onlyAllowed(address, uint256) external envfree;
    function _.onlyAllowed(address, uint256) external => DISPATCHER(true);
    function AllowlistV1.isDenied(address) external returns (bool) envfree;
    function _.isDenied(address) external => DISPATCHER(true);

    // RedeemManagerV1
    function RedeemManagerV1Harness.resolveRedeemRequests(uint32[]) external returns(int64[]) envfree;
    function _.resolveRedeemRequests(uint32[]) external => DISPATCHER(true);
     // requestRedeem function is also defined in River:
    // function _.requestRedeem(uint256) external => DISPATCHER(true); //not required, todo: remove
    function _.requestRedeem(uint256 _lsETHAmount, address _recipient) external => DISPATCHER(true);
    function _.claimRedeemRequests(uint32[], uint32[], bool, uint16) external => DISPATCHER(true);
    // function _.claimRedeemRequests(uint32[], uint32[]) external => DISPATCHER(true); //not required, todo: remove
    function _.pullExceedingEth(uint256) external => DISPATCHER(true);
    function _.reportWithdraw(uint256) external => DISPATCHER(true);
    function RedeemManagerV1Harness.getRedeemDemand() external returns (uint256) envfree;
    function _.getRedeemDemand() external => DISPATCHER(true);

    // RiverV1
    function getBalanceToDeposit() external returns(uint256) envfree optional;
    function getCommittedBalance() external returns(uint256) envfree optional;
    function getBalanceToRedeem() external returns(uint256) envfree optional;
    function consensusLayerDepositSize() external returns(uint256) envfree optional;
    function riverEthBalance() external returns(uint256) envfree optional;
    function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    function _.getAllowlist() external => DISPATCHER(true);
    function RiverV1Harness.getAllowlist() external returns(address) envfree;
    function _.sendCLFunds() external => DISPATCHER(true);
    function _.sendCoverageFunds() external => DISPATCHER(true);
    function _.sendELFees() external => DISPATCHER(true);

    // RiverV1 : SharesManagerV1
    function _.transfer(address, uint256) external => DISPATCHER(true);
    function _.transferFrom(address, address, uint256) external => DISPATCHER(true);
    function _.underlyingBalanceFromShares(uint256) external => DISPATCHER(true);
    function RiverV1Harness.underlyingBalanceFromShares(uint256) external returns(uint256) envfree;
    function _.balanceOfUnderlying(address) external => DISPATCHER(true);
    // function RiverV1Harness.balanceOfUnderlying(address) external returns(uint256) envfree;
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
    //function OperatorsRegistryV1.getStoppedAndRequestedExitCounts() external returns (uint32, uint256) envfree;
    function _.getStoppedAndRequestedExitCounts() external => DISPATCHER(true);
    function _.demandValidatorExits(uint256, uint256) external => DISPATCHER(true);
    function _.pickNextValidatorsToDeposit(uint256) external => DISPATCHER(true); // has no effect - CERT-4615

    function _.deposit(bytes,bytes,bytes,bytes32) external => DISPATCHER(true); // has no effect - CERT-4615

    // function _.increment_onDepositCounter() external => ghostUpdate_onDepositCounter() expect bool ALL;

    // MathSummarizations
    // function _.mulDivDown(uint256 a, uint256 b, uint256 c) internal => mulDivDownAbstractPlus(a, b, c) expect uint256 ALL;

    //workaroun per CERT-4615
    function LibBytes.slice(bytes memory _bytes, uint256 _start, uint256 _length) internal returns (bytes memory) => bytesSliceSummary(_bytes, _start, _length);
    // WLSETH
    function WLSETHV1.totalSupply() external returns(uint256) envfree;
    function WLSETHV1.balanceOf(address) external returns(uint256) envfree;
    function WLSETHV1.sharesOf(address) external returns(uint256) envfree;

}

ghost mapping(bytes32 => mapping(uint => bytes32)) sliceGhost;

function bytesSliceSummary(bytes buffer, uint256 start, uint256 len) returns bytes {
	bytes to_ret;
	require(to_ret.length == len);
	require(buffer.length <= require_uint256(start + len));
	bytes32 buffer_hash = keccak256(buffer);
	require keccak256(to_ret) == sliceGhost[buffer_hash][start];
	return to_ret;
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

invariant zeroAssetsZeroShares_invariant()
    RH.totalUnderlyingSupply() == 0 <=> RH.totalSupply() == 0;

invariant sharesOfEqualsLSETH(env e, address usr)
    sharesOf(usr) == RH.balanceOf(usr)
    {
        preserved
        {
            mathint w_shares = sharesOf(usr);
            mathint river_balance = RH.balanceOf(usr);
            mathint w_balance = balanceOf(usr);
            mathint river_balanceOfUnderlying = RH.balanceOfUnderlying(e, usr);
            require RH.totalUnderlyingSupply() <= 2^128;
            require RH.totalSupply() <= 2^128;
            require totalSupply() <= 2^128;
            requireInvariant zeroAssetsZeroShares_invariant;
        }
    }

rule testingRule(env e, method f, calldataarg args)
{
    address usr;
    mathint w_shares_before = sharesOf(usr);
    mathint river_balance_before = RH.balanceOf(usr);
    mathint w_balance_before = balanceOf(usr);

    f(e, args);

    mathint w_shares_after = sharesOf(usr);
    mathint river_balance_after = RH.balanceOf(usr);
    mathint w_balance_after = balanceOf(usr);

    assert w_shares_before != w_shares_after;
    assert river_balance_before != river_balance_after;
    assert w_balance_before != w_balance_after;
}

rule mintPayedAppropriately(env e)
{
    address recipient;
    uint256 amount_of_shares;
    mathint w_shares_before = sharesOf(recipient);
    mathint river_balance_before_msgSender = RH.balanceOf(e.msg.sender);
        mathint w_balance_before = balanceOf(recipient);
        mathint w_balance_before_msgSender = balanceOf(e.msg.sender);

    // require e.msg.sender != currentContract;

    mint(e, recipient, amount_of_shares);

    mathint w_shares_after = sharesOf(recipient);
    mathint river_balance_after_msgSender = RH.balanceOf(e.msg.sender);
        mathint w_balance_after = balanceOf(recipient);
        mathint w_balance_after_msgSender = balanceOf(e.msg.sender);

    assert river_balance_before_msgSender >= to_mathint(amount_of_shares);
    assert river_balance_before_msgSender - river_balance_after_msgSender == w_shares_after - w_shares_before;
    assert river_balance_before_msgSender - river_balance_after_msgSender == to_mathint(amount_of_shares);
    // assert w_balance_before - w_balance_after == w_shares_after - w_shares_before; // wrong
}

rule burnPaysAppropriately(env e)
{
    address recipient;
    uint256 amount_of_shares;
    mathint w_shares_before_msgSender = sharesOf(e.msg.sender);
    mathint river_balance_before = RH.balanceOf(recipient);
        mathint w_balance_before = balanceOf(recipient);

    // require e.msg.sender != currentContract;

    burn(e, recipient, amount_of_shares);

    mathint w_shares_after_msgSender = sharesOf(e.msg.sender);
    mathint river_balance_after = RH.balanceOf(recipient);
        mathint w_balance_after = balanceOf(recipient);

    assert w_shares_before_msgSender >= to_mathint(amount_of_shares);
    assert w_shares_before_msgSender - w_shares_after_msgSender == river_balance_after - river_balance_before;
    assert w_shares_before_msgSender - w_shares_after_msgSender == to_mathint(amount_of_shares);
}
