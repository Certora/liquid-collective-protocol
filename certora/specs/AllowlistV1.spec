import "Sanity.spec";

use rule method_reachability;

methods {
    // Allowlist
    function isAllowed(address, uint256) external returns(bool) envfree;
    function isDenied(address) external returns(bool) envfree;
}

/// @title isAllowed() only changes when setAllowPermissions or setDenyPermissions are called
rule isAllowedChangeRestrictively(env e, method f)
{
    address account;
    uint256 mask;
    bool isAllowedBefore = isAllowed(account, mask);
    calldataarg args;

    f(e, args);
    
    bool isAllowedAfter = isAllowed(account, mask);
    
    assert isAllowedAfter != isAllowedBefore =>
        f.selector == sig:setAllowPermissions(address[],uint256[]).selector ||
        f.selector == sig:setDenyPermissions(address[],uint256[]).selector;
}


/// @title isDenied() only changes when setAllowPermissions or setDenyPermissions is called
rule isDeniedChangeRestrictively(env e, method f)
{
    address account;
    bool isDeniedBefore = isDenied(account);
    calldataarg args;

    f(e, args);
    
    bool isDeniedAfter = isDenied(account);
    
    assert isDeniedAfter != isDeniedBefore =>
        f.selector == sig:setAllowPermissions(address[],uint256[]).selector ||
        f.selector == sig:setDenyPermissions(address[],uint256[]).selector;
}