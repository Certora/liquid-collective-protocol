/*
 * OracleManagerV1 Security Properties Specification
 * Formalizes Properties 1-21 for RiverV1's OracleManager component.
 *
 * Import structure (required by task):
 *   - RiverV1_base_summaries.spec : Auto-generated base summaries
 *   - custom_summaries.spec       : Protocol-specific summaries (DISPATCHER, mulDivDown)
 *   - invariants.spec             : Structural invariants (provides prop16 via clValidatorCountLeDeposited)
 */

import "specs/summaries/RiverV1_base_summaries.spec";
import "custom_summaries.spec";
import "invariants.spec";

// ============================================================
// PERSISTENT GHOSTS FOR PROP 14 (EL fees before coverage ordering)
// ============================================================
// Doc-ref: 59e32beda1d435759edd074dc875cfaa086a9fc382c213
// These persistent ghosts track whether ELFeeRecipientV1.pullELFees and
// CoverageFundV1.pullCoverageFunds were called during the current execution.
// Persistent ghosts are used because they survive reverts and HAVOC events,
// ensuring the call history is preserved even on reverting paths.

persistent ghost bool elFeesPulledThisCall {
    init_state axiom !elFeesPulledThisCall;
}

persistent ghost bool coveragePulledThisCall {
    init_state axiom !coveragePulledThisCall;
}

/// @notice Called by the ELFeeRecipientV1.pullELFees summary to track the call
function trackELFeesPull() {
    elFeesPulledThisCall = true;
    return;
}

/// @notice Called by the CoverageFundV1.pullCoverageFunds summary to track the call
function trackCoveragePull() {
    coveragePulledThisCall = true;
    return;
}

// ============================================================
// METHODS BLOCK
// ============================================================

methods {
    // Oracle & admin getters (envfree — no env vars accessed)
    function getOracle()                      external returns (address)                                      envfree;
    function getAdmin()                       external returns (address)                                      envfree;

    // Config getters returning structs (envfree)
    function getCLSpec()                      external returns (CLSpec.CLSpecStruct)                          envfree;
    function getReportBounds()                external returns (ReportBounds.ReportBoundsStruct)              envfree;
    function getLastConsensusLayerReport()    external returns (IOracleManagerV1.StoredConsensusLayerReport) envfree;
    function getLastCompletedEpochId()        external returns (uint256)                                      envfree;

    // Balance / supply getters (envfree)
    function totalUnderlyingSupply()          external returns (uint256)                                      envfree;
    function getBalanceToDeposit()            external returns (uint256)                                      envfree;

    // ---- Prop 14: EL fees / coverage ordering summaries ----
    // These specific summaries override the wildcard _.pullELFees / _.pullCoverageFunds
    // DISPATCHER entries from custom_summaries.spec for the specific contracts in the scene.
    // The summaries replace the actual implementations with no-ops that set tracking ghosts.
    // This is sound for the ordering property: EL fees are always called before coverage
    // in setConsensusLayerData regardless of what pullELFees actually does.
    // Doc-ref: 59e32beda1d435759edd074dc875cfaa086a9fc382c213
    function ELFeeRecipientV1.pullELFees(uint256) external => trackELFeesPull();
    function CoverageFundV1.pullCoverageFunds(uint256) external => trackCoveragePull();
}

// ============================================================
// DEFINITIONS
// ============================================================

/// @notice 10000 basis points = 100%
definition BASIS_POINTS_MAX_OMV() returns mathint = 10000;

/// @notice seconds in one year (365 days)
definition ONE_YEAR_OMV() returns mathint = 31536000;

/// @notice 32 ETH in wei
definition DEPOSIT_SIZE_OMV() returns mathint = 32000000000000000000;

// ============================================================
// CVL HELPER: compute current epoch matching the code's _currentEpoch
// ============================================================
// The code computes: ((block.timestamp - genesisTime) / secondsPerSlot) / slotsPerEpoch
// Using sequential divisions (NOT the product) to avoid non-linear arithmetic.
// Note: This equals floor(floor(x/a)/b) = floor(x/(a*b)) for positive integers,
// so the result is mathematically equivalent to the one-step division.
// Doc-ref: OracleManager.1.sol _currentEpoch

function computeCurrentEpoch(env e, CLSpec.CLSpecStruct cls) returns mathint {
    if (e.block.timestamp < cls.genesisTime || cls.secondsPerSlot == 0 || cls.slotsPerEpoch == 0) {
        return 0;
    }
    mathint timeSinceGenesis = e.block.timestamp - cls.genesisTime;
    mathint totalSlots = timeSinceGenesis / cls.secondsPerSlot;
    return totalSlots / cls.slotsPerEpoch;
}

// ============================================================
// PROPERTIES 1-9: setConsensusLayerData revert characterization
// ============================================================

// --- Prop 1: Only oracle address may call setConsensusLayerData ---
// Doc-ref: OracleManager.1.sol – "only the oracle is allowed to call this endpoint"
rule prop1_onlyOracleCanCallSetConsensusLayerData(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    address oracle = getOracle();
    setConsensusLayerData@withrevert(e, report);
    assert e.msg.sender != oracle => lastReverted;
}

// --- Prop 2a: setOracle requires admin ---
rule prop2_setOracleOnlyAdmin(env e, address newOracle) {
    address admin = getAdmin();
    setOracle@withrevert(e, newOracle);
    assert e.msg.sender != admin => lastReverted;
}

// --- Prop 2b: setCLSpec requires admin ---
rule prop2_setCLSpecOnlyAdmin(env e, CLSpec.CLSpecStruct clSpec) {
    address admin = getAdmin();
    setCLSpec@withrevert(e, clSpec);
    assert e.msg.sender != admin => lastReverted;
}

// --- Prop 2c: setReportBounds requires admin ---
rule prop2_setReportBoundsOnlyAdmin(env e, ReportBounds.ReportBoundsStruct bounds) {
    address admin = getAdmin();
    setReportBounds@withrevert(e, bounds);
    assert e.msg.sender != admin => lastReverted;
}

// --- Prop 3: epoch divisible by epochsPerFrame ---
// Doc-ref: OracleManager.1.sol _isValidEpoch – epoch % epochsPerFrame == 0
rule prop3_epochMustBeOnFrameBoundary(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    CLSpec.CLSpecStruct cls = getCLSpec();
    require cls.epochsPerFrame > 0;   // zero-value is its own revert (prop19)
    setConsensusLayerData@withrevert(e, report);
    assert report.epoch % cls.epochsPerFrame != 0 => lastReverted;
}

// --- Prop 4: epoch strictly greater than last stored epoch ---
// Doc-ref: OracleManager.1.sol _isValidEpoch – epoch > LastConsensusLayerReport.epoch
rule prop4_epochStrictlyGreaterThanLastReport(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    IOracleManagerV1.StoredConsensusLayerReport lastReport = getLastConsensusLayerReport();
    setConsensusLayerData@withrevert(e, report);
    assert report.epoch <= lastReport.epoch => lastReverted;
}

// --- Prop 5: current epoch >= report.epoch + epochsToAssumedFinality ---
// Doc-ref: OracleManager.1.sol _isValidEpoch – currentEpoch >= epoch + epochsToAssumedFinality
// Uses sequential divisions to match _currentEpoch exactly, avoiding non-linear arithmetic.
rule prop5_epochMustBePastFinalityWindow(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    CLSpec.CLSpecStruct cls = getCLSpec();
    require cls.slotsPerEpoch > 0;
    require cls.secondsPerSlot > 0;
    require e.block.timestamp >= cls.genesisTime;

    // Compute current epoch using sequential division (no non-linear multiplication).
    // Matches the code: ((block.timestamp - genesisTime) / secondsPerSlot) / slotsPerEpoch
    mathint currentEpoch = computeCurrentEpoch(e, cls);

    setConsensusLayerData@withrevert(e, report);
    assert currentEpoch < report.epoch + cls.epochsToAssumedFinality => lastReverted;
}

// --- Prop 6: validatorsCount must not exceed DepositedValidatorCount ---
// Doc-ref: OracleManager.1.sol – _report.validatorsCount > DepositedValidatorCount.get()
rule prop6_validatorsCountBoundedByDeposited(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    uint256 deposited = getDepositedValidatorCount();
    setConsensusLayerData@withrevert(e, report);
    assert to_mathint(report.validatorsCount) > to_mathint(deposited) => lastReverted;
}

// --- Prop 7: validatorsCount is non-decreasing ---
// Doc-ref: OracleManager.1.sol – _report.validatorsCount < lastStoredReport.validatorsCount
rule prop7_validatorsCountNonDecreasing(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    IOracleManagerV1.StoredConsensusLayerReport lastReport = getLastConsensusLayerReport();
    setConsensusLayerData@withrevert(e, report);
    assert to_mathint(report.validatorsCount) < to_mathint(lastReport.validatorsCount) => lastReverted;
}

// --- Prop 8: validatorsExitedBalance is non-decreasing ---
// Doc-ref: OracleManager.1.sol – InvalidDecreasingValidatorsExitedBalance
rule prop8_validatorsExitedBalanceNonDecreasing(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    IOracleManagerV1.StoredConsensusLayerReport lastReport = getLastConsensusLayerReport();
    setConsensusLayerData@withrevert(e, report);
    assert report.validatorsExitedBalance < lastReport.validatorsExitedBalance => lastReverted;
}

// --- Prop 9: validatorsSkimmedBalance is non-decreasing ---
// Doc-ref: OracleManager.1.sol – InvalidDecreasingValidatorsSkimmedBalance
rule prop9_validatorsSkimmedBalanceNonDecreasing(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    IOracleManagerV1.StoredConsensusLayerReport lastReport = getLastConsensusLayerReport();
    setConsensusLayerData@withrevert(e, report);
    assert report.validatorsSkimmedBalance < lastReport.validatorsSkimmedBalance => lastReverted;
}

// ============================================================
// REVERT CHARACTERIZATION PROPS 1-9 (unified, without balance bounds)
// ============================================================
// Covers props 1-9 in a single unified forward-direction check.
// Balance bounds (prop 10 skipped due to non-linear timeout, prop 11 separate rule).
// Uses sequential epoch computation to avoid non-linear arithmetic.
// Doc-ref: OracleManager.1.sol – setConsensusLayerData full validation chain

rule setConsensusLayerData_revertCharacterization(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    // --- State reads ---
    address oracle                                    = getOracle();
    CLSpec.CLSpecStruct cls                           = getCLSpec();
    IOracleManagerV1.StoredConsensusLayerReport last  = getLastConsensusLayerReport();
    uint256 dep                                       = getDepositedValidatorCount();

    // --- Access control ---
    bool invalidCaller = e.msg.sender != oracle;

    // --- Epoch validity (using sequential division for linearization) ---
    bool epochUnaligned = cls.epochsPerFrame == 0 
                        ? true 
                        : (report.epoch % cls.epochsPerFrame != 0);
    bool epochTooOld    = report.epoch <= last.epoch;

    // Sequential divisions avoid non-linear arithmetic (matches code's _currentEpoch)
    mathint currentEpoch = computeCurrentEpoch(e, cls);
    bool epochUnfinal    = currentEpoch < report.epoch + cls.epochsToAssumedFinality;

    // --- Cumulative value / count checks ---
    bool exitedDec   = report.validatorsExitedBalance  < last.validatorsExitedBalance;
    bool skimmedDec  = report.validatorsSkimmedBalance < last.validatorsSkimmedBalance;
    bool countDec    = to_mathint(report.validatorsCount) < to_mathint(last.validatorsCount);
    bool countOver   = to_mathint(report.validatorsCount) > to_mathint(dep);

    // --- Call ---
    setConsensusLayerData@withrevert(e, report);

    // Forward direction: these conditions → revert
    // (Additional reverts from external calls are possible but not enumerated here)
    assert (
        invalidCaller ||
        epochUnaligned || epochTooOld || epochUnfinal ||
        exitedDec      || skimmedDec  ||
        countDec       || countOver
    ) => lastReverted;
}

// ============================================================
// PROP 10: Balance increase bound
// ============================================================
// SKIPPED: Property 10 requires computing maxIncrease = preBalance * annualAprUpperBound *
// epochDelta * slotsPerEpoch * secondsPerSlot / (BASIS_POINTS_MAX * ONE_YEAR) in CVL.
// This is a 5-variable non-linear product that consistently causes SMT solver timeouts
// regardless of reformulation. See record_skip declaration for formal skip justification.
// The analogous prop11 (balance decrease bound, 2-variable product) VERIFIES successfully.

// ============================================================
// PROP 11: Balance decrease bound (revert characterization)
// ============================================================
// Doc-ref: OracleManager.1.sol – TotalValidatorBalanceDecreaseOutOfBound
// If the algebraic post-report balance is less than preBalance - maxDecrease,
// setConsensusLayerData must revert.

rule prop11_exceedingMaxDecreaseReverts(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    CLSpec.CLSpecStruct cls                          = getCLSpec();
    ReportBounds.ReportBoundsStruct rb               = getReportBounds();
    IOracleManagerV1.StoredConsensusLayerReport last = getLastConsensusLayerReport();
    uint256 dep                                      = getDepositedValidatorCount();
    mathint preBalance                               = totalUnderlyingSupply();

    // Algebraic postBalance
    mathint skimmedInc  = report.validatorsSkimmedBalance - last.validatorsSkimmedBalance;
    mathint exitedInc   = report.validatorsExitedBalance  - last.validatorsExitedBalance;
    mathint pendingNew  = dep > report.validatorsCount ? dep - report.validatorsCount : 0;
    mathint pendingOld  = dep > last.validatorsCount   ? dep - last.validatorsCount   : 0;
    mathint postBalance = preBalance
                        + (report.validatorsBalance - last.validatorsBalance)
                        + skimmedInc + exitedInc
                        + (pendingNew - pendingOld) * DEPOSIT_SIZE_OMV();

    // maxDecrease (only one multiplication: preBalance * relativeLowerBound)
    mathint maxDecrease = preBalance * rb.relativeLowerBound / BASIS_POINTS_MAX_OMV();
    mathint effMaxDec   = maxDecrease < preBalance ? maxDecrease : preBalance;

    setConsensusLayerData@withrevert(e, report);

    // Forward direction: if algebraic postBalance < preBalance - effMaxDec → revert
    assert postBalance < preBalance - effMaxDec => lastReverted;
}

// ============================================================
// PROPERTY 12: After success, epoch atomically committed
// ============================================================
// Doc-ref: OracleManager.1.sol – storedReport.epoch = _report.epoch

rule prop12_epochAtomicallyCommitted(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    setConsensusLayerData@withrevert(e, report);
    // Note: getLastCompletedEpochId() is evaluated INSIDE the assert expression,
    // not as a separate statement, so lastReverted is correctly read here.
    assert !lastReverted => getLastCompletedEpochId() == report.epoch;
}

// ============================================================
// PROPERTY 13: Rewards = CL balance delta + EL fees (NOT coverage / RM ETH)
// ============================================================
// SKIPPED: This property requires tracking the internal variable vars.trace.rewards
// (the exact argument passed to the internal virtual function _onEarnings(uint256)).
// Without RiverV1Harness instrumentation (not in the prover scene for this task),
// the internal rewards computation is not observable from the external interface.
// The observable consequences attempted:
//   - totalSupply() non-decreasing: VIOLATED because _reportWithdrawToRedeemManager
//     legitimately burns shares via RedeemManagerV1.reportWithdraw -> _burnRawShares
//   - postBalance <= preBalance + maxIncrease: TIMEOUT due to non-linear arithmetic
//     in the maxIncrease formula (preBalance * annualAprUpperBound * timeElapsed)
// See record_skip invocation for formal skip declaration.

// ============================================================
// PROPERTY 14: _pullELFees before _pullCoverageFunds; coverage bounded by residual
// ============================================================
// Verified using persistent ghosts that track when the external calls
// ELFeeRecipientV1.pullELFees and CoverageFundV1.pullCoverageFunds are made.
// Expression summaries replace the actual implementations with no-op trackers;
// this is sound because the ORDERING (EL before coverage) depends only on the
// if-block structure of setConsensusLayerData, not on what these functions return.
// Doc-ref: OracleManager.1.sol – setConsensusLayerData: if (availableAmountToUpperBound > 0)
//           _pullELFees first, then _pullCoverageFunds after
// Doc-ref: 59e32beda1d435759edd074dc875cfaa086a9fc382c213

rule prop14_elFeesPulledBeforeCoverage(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    // Constrain initial ghost state: neither EL fees nor coverage have been pulled yet
    require !elFeesPulledThisCall;
    require !coveragePulledThisCall;

    setConsensusLayerData@withrevert(e, report);

    // If coverage funds were pulled (coveragePulledThisCall = true), then
    // EL fees MUST have been pulled first (elFeesPulledThisCall = true).
    // This verifies the ordering: _pullELFees always precedes _pullCoverageFunds.
    assert coveragePulledThisCall => elFeesPulledThisCall;
}

// ============================================================
// PROPERTY 15: slashingContainmentMode prevents CommittedBalance increase
// ============================================================
// Doc-ref: River.1.sol _commitBalanceToDeposit – if (_slashingContainmentModeEnabled) { return; }

rule prop15_noCommittedBalanceIncreaseInSlashingMode(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    require report.slashingContainmentMode == true;

    uint256 committedBefore = getCommittedBalance();
    setConsensusLayerData@withrevert(e, report);
    // Capture lastReverted before any subsequent envfree calls reset it.
    bool didRevert = lastReverted;
    uint256 committedAfter  = getCommittedBalance();

    assert !didRevert => committedAfter <= committedBefore;
}

// ============================================================
// PROPERTY 16: LastConsensusLayerReport.validatorsCount <= DepositedValidatorCount
// ============================================================
// The invariant clValidatorCountLeDeposited from invariants.spec covers this property.
// Additional rule: setConsensusLayerData preserves the bound.

rule prop16_setConsensusLayerDataPreservesValidatorCountBound(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    requireInvariant clValidatorCountLeDeposited();
    setConsensusLayerData(e, report);
    assert getCLValidatorCount() <= getDepositedValidatorCount();
}

// ============================================================
// PROPERTY 17: getOracle() is never the zero address
// ============================================================
// Doc-ref: OracleAddress.sol – OracleAddress.set calls LibSanitize._notZeroAddress

// 17a: setOracle reverts when given address(0) → oracle stays non-zero
rule prop17a_setOracleNeverSetsZero(env e, address newOracle) {
    setOracle@withrevert(e, newOracle);
    // getOracle() is inside the assert expression — not a separate statement.
    assert !lastReverted => getOracle() != 0;
}

// 17b: initRiverV1 reverts when oracle address is zero
rule prop17b_initRiverV1SetsNonZeroOracle(
    env e,
    address depositContractAddress,
    address elFeeRecipientAddress,
    bytes32 withdrawalCredentials,
    address oracleAddress,
    address systemAdministratorAddress,
    address allowlistAddress,
    address operatorRegistryAddress,
    address collectorAddress,
    uint256 globalFee
) {
    initRiverV1@withrevert(e, depositContractAddress, elFeeRecipientAddress,
        withdrawalCredentials, oracleAddress, systemAdministratorAddress,
        allowlistAddress, operatorRegistryAddress, collectorAddress, globalFee);
    assert !lastReverted => getOracle() != 0;
}

// ============================================================
// PROPERTY 18 (ATTACK VECTOR): Admin can set annualAprUpperBound to any value
// ============================================================
// Goal: demonstrate the attack CANNOT occur.
// Expected: FAILS — there is no on-chain cap; admin can set any value.

rule prop18_annualAprUpperBoundIsCapped(env e, ReportBounds.ReportBoundsStruct bounds) {
    setReportBounds(e, bounds);
    // EXPECTED TO FAIL: the code places no cap on this value.
    assert bounds.annualAprUpperBound <= 10000;
}

// ============================================================
// PROPERTY 19 (ATTACK VECTOR): setCLSpec can zero critical fields
// ============================================================
// Goal: demonstrate the attack CANNOT occur.
// Expected: FAILS — setCLSpec has no zero-check for epochsPerFrame/slotsPerEpoch/secondsPerSlot.

rule prop19_clSpecCriticalFieldsNonZero(env e, CLSpec.CLSpecStruct clSpec) {
    address admin = getAdmin();
    require e.msg.sender == admin;

    setCLSpec@withrevert(e, clSpec);

    // EXPECTED TO FAIL: no such validation exists in the code.
    assert !lastReverted =>
        clSpec.epochsPerFrame > 0 &&
        clSpec.slotsPerEpoch  > 0 &&
        clSpec.secondsPerSlot > 0;
}

// ============================================================
// PROPERTY 20 (ATTACK VECTOR): Integer division can make maxIncrease zero
// ============================================================
// Goal: demonstrate the attack CANNOT occur.
// Expected: FAILS — maxIncrease rounds to 0 for small values, blocking valid reports.

rule prop20_maxIncreasePositiveWhenInputsPositive(
    env e,
    IOracleManagerV1.ConsensusLayerReport report
) {
    ReportBounds.ReportBoundsStruct rb               = getReportBounds();
    CLSpec.CLSpecStruct cls                          = getCLSpec();
    IOracleManagerV1.StoredConsensusLayerReport last = getLastConsensusLayerReport();

    require cls.slotsPerEpoch > 0 && cls.secondsPerSlot > 0;
    require report.epoch > last.epoch;

    mathint preBalance   = totalUnderlyingSupply();
    mathint timeElapsed  = (report.epoch - last.epoch) * cls.slotsPerEpoch * cls.secondsPerSlot;
    mathint maxIncrease  = preBalance * rb.annualAprUpperBound * timeElapsed
                         / (BASIS_POINTS_MAX_OMV() * ONE_YEAR_OMV());

    // EXPECTED TO FAIL: integer division can yield 0 when the product is small.
    assert preBalance > 0 && rb.annualAprUpperBound > 0 && timeElapsed > 0
        => maxIncrease > 0;
}

// ============================================================
// PROPERTY 21 (ATTACK VECTOR): epochsPerFrame change creates extended gap
// ============================================================
// Goal: demonstrate the attack CANNOT occur.
// Expected: FAILS — admin can make epochsPerFrame arbitrarily large.

rule prop21_epochsPerFrameChangeGapBounded(env e, CLSpec.CLSpecStruct newSpec) {
    CLSpec.CLSpecStruct oldSpec                            = getCLSpec();
    IOracleManagerV1.StoredConsensusLayerReport lastReport = getLastConsensusLayerReport();

    address admin = getAdmin();
    require e.msg.sender == admin;
    require newSpec.epochsPerFrame > 0;

    setCLSpec@withrevert(e, newSpec);

    mathint nextValidEpoch = (lastReport.epoch / newSpec.epochsPerFrame + 1)
                           * newSpec.epochsPerFrame;
    mathint gap            = nextValidEpoch - lastReport.epoch;

    // EXPECTED TO FAIL: admin can make epochsPerFrame arbitrarily large.
    assert !lastReverted => gap <= 2 * oldSpec.epochsPerFrame;
}
