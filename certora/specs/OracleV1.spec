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

    /// IOracleManager
    function _.setConsensusLayerData(IOracleManagerV1.ConsensusLayerReport report) external with (env e) => setEpochCVL(report.epoch, e) expect void;
    function _.isValidEpoch(uint256 epoch) external with (env e) => isValidEpochCVL(epoch, e.block.timestamp) expect bool;
}
/// Verification report:
/// https://prover.certora.com/output/41958/53fadabba0a34488818c961a7dc424d5/?anonymousKey=ff982a2fecbcb60d0b3744d38ee39721169fdcf4

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Definitions                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

definition ZERO_ADDRESS() returns address = 0;

definition noMemberDuplicates(address account1, address account2) returns bool = 
    (account1 != ZERO_ADDRESS() && account2 != ZERO_ADDRESS()) => account1 != account2;

definition changeMemberMethods(method f) returns bool = 
    f.selector == sig:setMember(address,address).selector ||
    f.selector == sig:removeMember(address,uint256).selector ||
    f.selector == sig:addMember(address,uint256).selector;

definition clearVariantsMethods(method f) returns bool = 
    f.selector == sig:initOracleV1_1().selector ||
    f.selector == sig:removeMember(address,uint256).selector ||
    f.selector == sig:addMember(address,uint256).selector ||
    f.selector == sig:setQuorum(uint256).selector ||
    f.selector == sig:reportConsensusLayerData(IOracleManagerV1.ConsensusLayerReport).selector;

definition initializeMethods(method f) returns bool = 
    f.selector == sig:initOracleV1(address,address,uint64,uint64,uint64,uint64,uint256,uint256).selector || 
    f.selector == sig:initOracleV1_1().selector;

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

/// An inconvenient way to enforce the no-duplicate invariants for several indices.
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

function RequireNoDuplicatesForAddressPair(address account1, address account2) {
    uint256 index1; uint256 index2; 
    requireInvariant ZeroAddressIsNotAMember();
    /// Tag 'index' to be the index of 'account':
    require isMember(account1) => getMemberAtIndex(index1) == account1;
    require isMember(account2) => getMemberAtIndex(index2) == account2;
    requireInvariant NoMembersDuplicates(index1, index2);
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Summaries: IOracleManager Mock                                                                                             │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
/// Mock for OracleManager.LastConsensusLayerReport.get().epoch
ghost uint256 lastConsensusEpoch {
    init_state axiom lastConsensusEpoch == 0;
}

/// Track the last timestamp in which the consensus report was submitted.
ghost uint256 lastConsensusTimestamp {
    init_state axiom lastConsensusTimestamp == 0;
}

/// Mock a part of OracleManager._isValidEpoch()
ghost _validEpochTime(uint256,uint256) returns bool {
    /// We assume that for every timestamp there exists only one valid epoch.
    /// That assumption strongly depends on the CLSpec of the River contract (e.g. the epochs per frame, the slots per epoch).
    /// If the oracle report is submitted every 24h, and the epochs per frame = 225, this condition is satisfied.
    axiom forall uint256 timestamp. forall uint256 epoch1. forall uint256 epoch2.
        (_validEpochTime(epoch1, timestamp) && _validEpochTime(epoch2, timestamp)) => epoch1 == epoch2;
    /// Epoch = 0 is not a valid epoch
    axiom forall uint256 timestamp. !_validEpochTime(0, timestamp);
}

function isValidEpochCVL(uint256 epoch, uint256 timestamp) returns bool {
    return _validEpochTime(epoch, timestamp) && epoch > lastConsensusEpoch;
}

/// Upon a call to setConsensusLayerData() the stored consensus report epoch is updated accordingly.
function setEpochCVL(uint256 epoch, env e) {
    require isValidEpochCVL(epoch, e.block.timestamp);
    lastConsensusEpoch = epoch;
    lastConsensusTimestamp = e.block.timestamp;
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

/// @title Only the admin can change the quorum.
rule onlyAdminChangesQuorum(method f) filtered{f -> !f.isView && !initializeMethods(f)} {
    uint256 quorum_before = getQuorum();
        env e;
        bool isSenderAdmin = e.msg.sender == getAdmin();
        calldataarg args;
        f(e,args);
    uint256 quorum_after = getQuorum();

    assert quorum_after != quorum_before => isSenderAdmin;
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules: Oracle members                                                                                                  │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/

/// @title The quorum value Q should respect the following invariant, where O is oracle member count
/// (O / 2) + 1 <= Q <= O
invariant QuorumBounds()
    getQuorum() <= getNumberOfMembers() && getQuorum() - 1 >= getNumberOfMembers() / 2 ;

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
            uint256 lastIndex = numberOfMembers == 0 ? 0 : assert_uint256(numberOfMembers-1);
            requireInvariant NoMembersDuplicates(index1, lastIndex);
            requireInvariant NoMembersDuplicates(index2, lastIndex);
        }
    }

/// @title lastReportedEpoch must be larger than the last consensus epoch.
invariant LastReportedEpochIsValid()
    lastConsensusTimestamp !=0 => (
        isValidEpochCVL(lastConsensusEpoch, lastConsensusTimestamp) &&
        getLastReportedEpochId() > lastConsensusEpoch
    )
    &&
    lastConsensusTimestamp ==0 <=> lastConsensusEpoch == 0
    {
        preserved with (env e) {require e.block.timestamp !=0;}
    }

/// @title Any report variant has non-zero votes.
invariant VariantHasVotes(uint256 id) 
    id < getReportVariantsCount() => getReportVariantDetails(id).votes > 0
    {
        preserved {
            requireInvariant ZeroAddressIsNotAMember();
            uint256 lastIndex = getReportVariantsCount() > 0 ? assert_uint256(getReportVariantsCount() - 1) : 0;
            requireInvariant VariantHasVotes(lastIndex);
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

rule votesChangeIntegrity(method f, uint256 id) filtered{f -> !f.isView && !clearVariantsMethods(f)} {
    env e;
    bool isMember_ = isMember(e.msg.sender);
    require getReportVariantsCount() < (1 << 254);
    ReportsVariants.ReportVariantDetails details_before = getReportVariantDetails(id);
    uint256 votes_before = details_before.votes;
        calldataarg args;
        f(e, args);
    ReportsVariants.ReportVariantDetails details_after = getReportVariantDetails(id);
    uint256 votes_after = details_after.votes;

    assert !isMember_ => votes_before == votes_after, "A non oracle member cannot change the number of votes";
    assert votes_before == votes_after || votes_after - votes_before == 1, "votes can either increase by 1 or be nullified";
}

rule votesChangeIntegrity_report(uint256 id) {
    env e;
    bool isMember_ = isMember(e.msg.sender);
    require getReportVariantsCount() < (1 << 254);
    ReportsVariants.ReportVariantDetails details_before = getReportVariantDetails(id);
    uint256 votes_before = details_before.votes;
        calldataarg args;
        requireInvariant VariantHasVotes(0);
        requireInvariant VariantHasVotes(1);
        requireInvariant VariantHasVotes(2);
        requireInvariant VariantHasVotes(3);
        requireInvariant VariantHasVotes(4);
        reportConsensusLayerData(e, args);
    ReportsVariants.ReportVariantDetails details_after = getReportVariantDetails(id);
    uint256 votes_after = details_after.votes;

    assert !isMember_ => votes_before == votes_after, "A non oracle member cannot change the number of votes";
    assert votes_before == votes_after || votes_after - votes_before == 1, "votes can either increase by 1 or be nullified";
}

/*
┌─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
│ Rules : Reports                                                                                           │
└─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
*/
rule initialize1ClearsReports() {
    env e;
    calldataarg args;
    initOracleV1_1(e, args);
    assert getReportVariantsCount() == 0;
}

rule whichMethodsClearVariants(method f) filtered{f -> !f.isView && !initializeMethods(f)} {
    env e;
    calldataarg args;
    require getReportVariantsCount() !=0;
    bool senderIsAdminOrMember = isMember(e.msg.sender) || e.msg.sender == getAdmin();
    f(e, args);
    
    assert getReportVariantsCount() == 0 => clearVariantsMethods(f);
    assert getReportVariantsCount() == 0 => senderIsAdminOrMember;
}

/// @title An oracle cannot submit reports in the same epoch (timestamp).
rule oracleCannotSubmitTwoReportsInTheSameEpoch() {
    IOracleManagerV1.ConsensusLayerReport reportA;
    IOracleManagerV1.ConsensusLayerReport reportB;
    uint256 lastEpoch = getLastReportedEpochId();
    env eA;
    env eB;
    requireInvariant LastReportedEpochIsValid();
    require eA.msg.sender == eB.msg.sender;
    reportConsensusLayerData(eA, reportA);
    reportConsensusLayerData@withrevert(eB, reportB);

    assert eA.block.timestamp == eB.block.timestamp => lastReverted;
}

/// @title Any submitted report ID must be after the last reported epoch. 
/// The last reported epoch ID must be updated to that of the report.
rule cannotSubmitEarlierEpoch() {
    IOracleManagerV1.ConsensusLayerReport report;
    uint256 lastEpoch_before = getLastReportedEpochId();
        env e;
        reportConsensusLayerData(e, report);
    uint256 lastEpoch_after = getLastReportedEpochId();

    assert report.epoch >= lastEpoch_before;
    assert report.epoch == lastEpoch_after || report.epoch + 1 == to_mathint(lastEpoch_after);
}

/// @title No one can front-run a submission of a report with the same report submission and make the second one revert.
rule cannotFrontRunSameReportSubmission(IOracleManagerV1.ConsensusLayerReport report) {
    env e1;
    env e2;
    RequireNoDuplicatesForAddressPair(e1.msg.sender, e2.msg.sender);
    storage initState = lastStorage;

    reportConsensusLayerData(e1, report) at initState;

    reportConsensusLayerData(e2, report) at initState;
    reportConsensusLayerData@withrevert(e1, report);

    assert e1.msg.sender != e2.msg.sender <=> !lastReverted;
}

/// @title Correctness of reportConsensusLayerData():
/// If the member has voted before, it can only vote again for a later epoch than the one which was last submitted.
rule reportSubmissionIntegrity1() {
    env e;
    IOracleManagerV1.ConsensusLayerReport report;
    uint256 lastConsensus_before = lastConsensusEpoch;
    uint256 lastSubmittedEpoch = getLastReportedEpochId();
    requireInvariant ZeroAddressIsNotAMember();
    RequireNoDuplicatesForAddress(e.msg.sender);
    requireInvariant LastReportedEpochIsValid();
    requireInvariant QuorumBounds();
    /// Safe assumption
    require e.block.timestamp >= lastConsensusTimestamp;

    bool status_before = getMemberReportStatus(e.msg.sender);
        reportConsensusLayerData@withrevert(e, report);
        bool reverted = lastReverted;
    bool status_after = getMemberReportStatus(e.msg.sender);
    uint256 lastConsensus_after = lastConsensusEpoch;

    assert status_before => (reverted || report.epoch > lastSubmittedEpoch);
}

/// @title Correctness of reportConsensusLayerData():
/// After the function call, the member status must be true, or result in the report being submitted to the river.
rule reportSubmissionIntegrity2() {
    env e;
    IOracleManagerV1.ConsensusLayerReport report;
    uint256 lastConsensus_before = lastConsensusEpoch;
    requireInvariant ZeroAddressIsNotAMember();
    RequireNoDuplicatesForAddress(e.msg.sender);
    requireInvariant LastReportedEpochIsValid();
    requireInvariant QuorumBounds();
    /// Safe assumption
    require e.block.timestamp >= lastConsensusTimestamp;

    reportConsensusLayerData(e, report);
    uint256 lastConsensus_after = lastConsensusEpoch;

    assert getMemberReportStatus(e.msg.sender) || lastConsensus_before != lastConsensus_after;
}

/// @title If a report has been submitted, then all votes must be nullified (no report variants).
rule submitReportNullifiesVotes() {
    require getReportVariantsCount() != 0;
    uint256 lastConsensus_before = lastConsensusEpoch;
        env e;
        calldataarg args;
        reportConsensusLayerData(e, args);
    uint256 lastConsensus_after = lastConsensusEpoch;
    assert lastConsensus_before != lastConsensus_after => getReportVariantsCount() == 0;
}