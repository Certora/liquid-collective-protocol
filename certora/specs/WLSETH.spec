import "Sanity.spec";
import "CVLMath.spec";

using RiverMock as river;

use rule method_reachability;

methods {
    // WLSETH
    function WLSETHV1.totalSupply() external returns (uint256) envfree;
    function WLSETHV1.balanceOf(address) external returns (uint256) envfree;
    function WLSETHV1.sharesOf(address) external returns (uint256) envfree;

    /// SharesManager
    function river.totalShares() external returns (uint256) envfree;
    function river.balanceOf(address) external returns (uint256) envfree;
    function river.assetBalance() external returns (uint256) envfree;
    function river.sharesPerOwner(address) external returns (uint256) envfree;
    function river.underlyingBalanceFromShares(uint256) external returns (uint256) envfree;
    function river.sharesFromUnderlyingBalance(uint256) external returns (uint256) envfree;
    function river.totalSupply() external returns (uint256) envfree;
    function river.totalUnderlyingSupply() external returns (uint256) envfree;

    /// Dispatch RiverMock
    function _.sendRedeemManagerExceedingFunds() external => DISPATCHER(true);
    function _.underlyingBalanceFromShares(uint256 _shares) external => DISPATCHER(true);
    function _.sharesFromUnderlyingBalance(uint256)  external => DISPATCHER(true);
    function _.transfer(address _to, uint256 _value) external => DISPATCHER(true);
    function _.transferFrom(address _from, address _to, uint256 _value) external => DISPATCHER(true);
    function _.balanceOfUnderlying(address _owner) external => DISPATCHER(true);
    function RiverMath.mulDiv(uint256 a, uint256 b, uint256 c) internal returns (uint256) => mulDivDownAbstractPlus(a, b, c);
}

invariant balanceOfLessOrEqualTotalSupply(env e, address usr)
    totalSupply() >= balanceOf(usr);

rule changeOfSharesIsChangeOfRiverBalance(address usr, method f) filtered{f -> !f.isView} {
    env e;
    require e.msg.sender != currentContract;
    address recipient;
    
    mathint w_shares_user_before = sharesOf(usr);
    mathint w_shares_recp_before = sharesOf(usr);
    mathint river_balance_before_recipient = river.balanceOf(recipient);
        calldataarg args;
        f(e, args);
    mathint w_shares_user_after = sharesOf(usr);
    mathint w_shares_recp_after = sharesOf(usr);
    mathint river_balance_after_recipient = river.balanceOf(recipient);

    assert river_balance_after_recipient - river_balance_before_recipient ==
        w_shares_user_before - w_shares_user_after;
}
    

rule mintPayedAppropriately(address recipient) {
    env e;
    uint256 amount_of_shares;
    mathint w_shares_before = sharesOf(recipient);
    mathint river_balance_before_msgSender = river.balanceOf(e.msg.sender);
    mathint w_balance_before = balanceOf(recipient);
    mathint w_balance_before_msgSender = balanceOf(e.msg.sender);

    require e.msg.sender != currentContract;

    mint(e, recipient, amount_of_shares);

    mathint w_shares_after = sharesOf(recipient);
    mathint river_balance_after_msgSender = river.balanceOf(e.msg.sender);
    mathint w_balance_after = balanceOf(recipient);
    mathint w_balance_after_msgSender = balanceOf(e.msg.sender);

    assert river_balance_before_msgSender >= to_mathint(amount_of_shares);
    assert river_balance_before_msgSender - river_balance_after_msgSender == w_shares_after - w_shares_before;
    assert river_balance_before_msgSender - river_balance_after_msgSender == to_mathint(amount_of_shares);
}

rule burnPaysAppropriately(address recipient) {
    env e;
    uint256 amount_of_shares;
    mathint w_shares_before_msgSender = sharesOf(e.msg.sender);
    mathint river_balance_before = river.balanceOf(recipient);
    mathint w_balance_before = balanceOf(recipient);

    require e.msg.sender != currentContract;

    burn(e, recipient, amount_of_shares);

    mathint w_shares_after_msgSender = sharesOf(e.msg.sender);
    mathint river_balance_after = river.balanceOf(recipient);
    mathint w_balance_after = balanceOf(recipient);

    if(recipient != currentContract) {
        assert w_shares_before_msgSender - w_shares_after_msgSender == river_balance_after - river_balance_before;
    }
    else {
        assert river_balance_after == river_balance_before;
    }
    assert w_shares_before_msgSender >= to_mathint(amount_of_shares); 
    assert w_shares_before_msgSender - w_shares_after_msgSender == to_mathint(amount_of_shares);
}
