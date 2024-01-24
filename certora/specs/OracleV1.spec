methods {
    /// IAdministrable
    function getAdmin() external returns (address) envfree;
    function getPendingAdmin() external returns (address) envfree;

    /// IOracleV1
    function getRiver() external returns (address) envfree;
    function getMemberReportStatus(address) external returns (bool) envfree;
    function getGlobalReportStatus() external returns (uint256) envfree;
    function getReportVariantsCount() external returns (uint256) envfree;
    function getReportVariantDetails(uint256) external returns (ReportsVariants.ReportVariantDetails memory) envfree;
    function getQuorum() external returns (uint256) envfree;
    function getOracleMembers() external returns (address[] memory) envfree;
    function isMember(address) external returns (bool) envfree;
    function getLastReportedEpochId() external returns (uint256) envfree;

    /// @notice Submit a report as an oracle member
    function reportConsensusLayerData(IOracleManagerV1.ConsensusLayerReport) external;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Definitions                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

definition ZERO_ADDRESS() returns address = 0;

definition noMemberDuplicates(address account1, address account2) returns bool = 
    (account1 !=0 && account2 !=0) => account1 != account2;

definition changeMemberMethods(method f) returns bool = 
    f.selector == sig:setMember(address,address).selector ||
    f.selector == sig:removeMember(address,uint256).selector ||
    f.selector == sig:addMember(address,uint256).selector;

definition initializeMethods(method f) returns bool = 
    f.selector == sig:initOracleV1(address,address,uint64,uint64,uint64,uint64,uint256,uint256).selector;


/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Helper functions : oracle members                                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

function getMemberAtIndex(uint256 index) returns address {
    address[] _members = getOracleMembers();
    return index < _members.length ? _members[index] : ZERO_ADDRESS();
}

function getNumberOfMembers() returns uint256 {
    address[] _members = getOracleMembers();
    return _members.length;
}

/// A non-convenient way to enforce the no-duplicate invariants for several indices.
/// Number of repetitions should comply with 'loop_iter'.
function RequireNoDuplicatesIndexPlus3(uint256 index) {
    uint256 N = getNumberOfMembers();
    requireInvariant NoMembersDuplicates(index, 0);
    requireInvariant NoMembersDuplicates(index, 1); 
    requireInvariant NoMembersDuplicates(index, 2);
    if(N > 0) {requireInvariant NoMembersDuplicates(index, assert_uint256(N-1));}
}

function RequireNoDuplicatesForAddress(address account) {
    uint256 index; 
    /// Tag 'index' to be the index of 'account':
    require account != ZERO_ADDRESS() => getMemberAtIndex(index) == account;
    RequireNoDuplicatesIndexPlus3(index);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: Admin                                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

/// @title Correctness of the acceptAdmin() function.
rule acceptAdminIntegrity() {
    env e;
    address adminBefore = getAdmin();
    address pendingAdminBefore = getPendingAdmin();
        acceptAdmin(e);
    address adminAfter = getAdmin();
    address pendingAdminAfter= getPendingAdmin();

    assert adminAfter == pendingAdminBefore, "The new admin must be the one proposed";
    assert e.msg.sender == pendingAdminBefore, "Only the proposed admin can accept";
    assert pendingAdminAfter == 0, "The pending admin must be zero after accepting";
}

/// @title Correctness of the proposeAdmin() function.
rule proposeAdminIntegrity(address account) {
    env e;
    address adminBefore = getAdmin();
    address pendingAdminBefore = getPendingAdmin();
        proposeAdmin(e, account);
    address adminAfter = getAdmin();
    address pendingAdminAfter= getPendingAdmin();

    assert adminBefore == adminAfter, "The admin cannot change while proposing a new one";
    assert e.msg.sender == adminBefore, "Only the admin can propose a new admin";
    assert pendingAdminAfter == account, "The pending admin must be  set correctly";
}

/// @title Only the pending admin or the admin can change the pending admin.
rule onlyPendingAdminOrAdminCanChangePendingAdmin(method f) filtered{f -> !f.isView} {
    address pendingAdminBefore = getPendingAdmin();
        env e;
        bool isSenderAdmin = e.msg.sender == getAdmin();
        bool isSenderPendingAdmin = e.msg.sender == pendingAdminBefore;
        calldataarg args;
        f(e,args);
    address pendingAdminAfter = getPendingAdmin();

    assert pendingAdminBefore != pendingAdminAfter => (isSenderAdmin || isSenderPendingAdmin);
}

/// @title Only the pending admin or the admin can change the admin.
/// @notice We assume that the initialization is controlled by a trusted party.
rule onlyPendingAdminOrAdminCanChangeAdmin(method f) filtered{f -> !f.isView && !initializeMethods(f)} {
    address adminBefore = getAdmin();
        env e;
        bool isSenderAdmin = e.msg.sender == adminBefore;
        bool isSenderPendingAdmin = e.msg.sender == getPendingAdmin();
        calldataarg args;
        f(e,args);
    address adminAfter = getAdmin();

    assert adminBefore != adminAfter => (isSenderAdmin || isSenderPendingAdmin);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: Oracle members                                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

/// @title The quorum cannot exceed the number of members.
invariant QuorumIsAtMostNumberOfMembers()
    getQuorum() <= getNumberOfMembers();

/// @title The zero address is never an oracle member.
invariant ZeroAddressIsNotAMember()
    !isMember(0);

/// @title No addresses duplicates in oracle members index.
invariant NoMembersDuplicates(uint256 index1, uint256 index2) 
    index1 != index2 => noMemberDuplicates(getMemberAtIndex(index1), getMemberAtIndex(index2))
    {
        preserved {
            uint256 numberOfMembers = getNumberOfMembers();
            require numberOfMembers < max_uint;
            if(numberOfMembers !=0 ) {
                requireInvariant NoMembersDuplicates(index1, assert_uint256(numberOfMembers-1));
                requireInvariant NoMembersDuplicates(index2, assert_uint256(numberOfMembers-1));
            }   
        }
    }
    
/// @title The setMember() function:
    /// (a) Cannot assign the same member again.
    /// (b) Doesn't set the zero address as the zero address.
    /// (c) Revokes the old member, only if it was a member before.
    /// (d) Add the new member, only if it was not a member before.
rule setMemberIntegrity(address currentMember, address newMember) {
    requireInvariant ZeroAddressIsNotAMember();
    RequireNoDuplicatesForAddress(currentMember);
    
    env e;
    bool isOldMember_before = isMember(currentMember);
    bool isNewMember_before = isMember(newMember);
        setMember(e, currentMember, newMember);
    bool isOldMember_after = isMember(currentMember);
    bool isNewMember_after = isMember(newMember);

    assert currentMember !=0, "Invariant sanity check";
    assert currentMember != newMember, "cannot reassign the same member";
    assert newMember != 0, "Cannot assign the zero address";
    assert isOldMember_before && !isOldMember_after, "Old member must be removed";
    assert !isNewMember_before && isNewMember_after, "New member must be added";
}

/// @title The oracle members array has no duplicates.
rule noDuplicatesInOracles(method f, uint256 indx1, uint256 indx2)
filtered{f -> changeMemberMethods(f)} {
    requireInvariant ZeroAddressIsNotAMember();

    address[] _members = getOracleMembers();
    uint256 numberOfMembers = _members.length;
    address member1 = indx1 < numberOfMembers ? _members[indx1] : ZERO_ADDRESS();
    address member2 = indx2 < numberOfMembers ? _members[indx2] : ZERO_ADDRESS();
    /// Assume no duplicates
    require noMemberDuplicates(member1, member2);

    /// Call any method that can change the isMember status
    env e;
    calldataarg args;
    f(e, args);

    // Assert no duplicates
    assert noMemberDuplicates(member1, member2);
}

/// @title An account cannot be added to the members list if it's already a member.
rule cannotAddIfAlreadyAMember(address account) {
    env e;
    uint256 newQuorum;
    bool isMember_before = isMember(account);
        addMember(e, account, newQuorum);
    bool isMember_after = isMember(account);
    assert !isMember_before && isMember_after;
}

/// @title An account cannot be removed from the members list if it's not a member.
rule cannotRemoveIfNotAMember(address account) {
    requireInvariant ZeroAddressIsNotAMember();
    RequireNoDuplicatesForAddress(account);
    
    env e;
    uint256 newQuorum;
    bool isMember_before = isMember(account);
        removeMember(e, account, newQuorum);
    bool isMember_after = isMember(account);
    assert isMember_before && !isMember_after;
}

/// @title only the setMember(), removeMember() and addMember() can change the isMember() status.
rule whichFunctionsChange_isMember(method f, address account) filtered{f -> !f.isView} {
    bool _isMember = isMember(account);
        env e;
        calldataarg args;
        f(e,args);
    bool isMember_ = isMember(account);

    assert _isMember != isMember_ => changeMemberMethods(f);
}

/// @title only the admin can add/remove members. Only a member can revoke himself.
rule whoCanChangeTheOracleMembers(method f, address account) filtered{f -> changeMemberMethods(f)} {
    env e;
    bool isSenderAdmin = e.msg.sender == getAdmin();
    bool _isMember = isMember(account);
    bool isSetMember = f.selector == sig:setMember(address,address).selector;
    address currentMember;
        
    if(isSetMember) {
        address newMember;
        setMember(e, currentMember, newMember);
    }
    else {
        calldataarg args;
        f(e, args);
    }
    bool isMember_ = isMember(account);

    assert (_isMember != isMember_) => (
        isSenderAdmin ||
        (isSetMember => currentMember == e.msg.sender)
    );
}

/// @title An actor who is not an admin cannot front-run and make setQuorum() revert.
/// @notice We assume that the initialization is controlled by a trusted party.
rule nonAdminCannotFrontRunSetQuorum(method f) filtered{f -> !f.isView && !initializeMethods(f)} {
    env e1; calldataarg args1;
    env e2; calldataarg args2;

    bool senderIsNotAnAdmin = !(getAdmin() == e2.msg.sender || getPendingAdmin() == e2.msg.sender); 

    storage initState = lastStorage;

    setQuorum(e1, args1) at initState;

    f(e2, args2) at initState;
    setQuorum@withrevert(e1, args1);

    assert senderIsNotAnAdmin => !lastReverted;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules : Reports                                                                                           │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
/// @title Any submitted report ID must be after the last reported epoch. 
/// The last reported epoch ID must be updated to that of the report.
rule cannotSubmitEarlierEpoch() {
    IOracleManagerV1.ConsensusLayerReport report;
    uint256 lastEpoch_before = getLastReportedEpochId();
        env e;
        reportConsensusLayerData(e, report);
    uint256 lastEpoch_after = getLastReportedEpochId();

    assert report.epoch > lastEpoch_before;
    assert report.epoch == lastEpoch_after;
}

/// @title One cannot submit the same report twice sequentially.
rule cannotSubmitSameReportTwice(method f) {
    IOracleManagerV1.ConsensusLayerReport report;
        env e1;
        env e2;
        reportConsensusLayerData(e1, report);
        reportConsensusLayerData@withrevert(e2, report);

    assert lastReverted;
}