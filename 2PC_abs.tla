---- MODULE 2PC_abs ----

EXTENDS TLAPS

CONSTANT VotingPhaseConsensuses
CONSTANT CommitPhaseDecisions
CONSTANT TransactionStatuses

VARIABLE votingPhaseConsensus
VARIABLE commitPhaseDecision
VARIABLE transactionStatus
VARIABLE failureDuringVotingPhase
ASSUME CommitPhaseDecisionsAssume ==
    CommitPhaseDecisions = {"Waiting", "Commit", "Abort"}

ASSUME VotingPhaseConsensusesAssume ==
    VotingPhaseConsensuses = {"NotAvailable", "Yes", "No"}

ASSUME TransactionStatusesAssume == 
    TransactionStatuses = {"InProgress", "Aborted", "Commited"}

vars == 
    <<
        failureDuringVotingPhase,
        votingPhaseConsensus,
        commitPhaseDecision,
        transactionStatus
    >>

TypeOK ==
    /\ failureDuringVotingPhase \in BOOLEAN 
    /\ transactionStatus \in TransactionStatuses
    /\ commitPhaseDecision \in CommitPhaseDecisions
    /\ votingPhaseConsensus \in VotingPhaseConsensuses

---------

FailCoordinator ==
    /\ votingPhaseConsensus = "NotAvailable"
    /\ failureDuringVotingPhase = FALSE
    /\ failureDuringVotingPhase' = TRUE
    /\ UNCHANGED << transactionStatus, votingPhaseConsensus, commitPhaseDecision >>

DetermineVoterConsensus ==
    /\ failureDuringVotingPhase = FALSE
    /\ votingPhaseConsensus = "NotAvailable"
    /\ \E cons \in VotingPhaseConsensuses \ {"NotAvailable"}:
        /\ votingPhaseConsensus' = cons
    /\ UNCHANGED << transactionStatus, commitPhaseDecision, failureDuringVotingPhase >>

ProcessVotingPhase ==
    /\ votingPhaseConsensus = "NotAvailable" 
    /\ failureDuringVotingPhase = FALSE
    /\ \/ FailCoordinator
       \/ DetermineVoterConsensus
    /\ UNCHANGED << transactionStatus, commitPhaseDecision >>

ProcessCommitPhase ==
    /\ \/ failureDuringVotingPhase = TRUE
       \/ votingPhaseConsensus # "NotAvailable"
    /\ commitPhaseDecision = "Waiting"
    /\ \/ /\ votingPhaseConsensus = "Yes"
          /\ commitPhaseDecision' = "Commit"
       \/ /\ votingPhaseConsensus # "Yes"
          /\ commitPhaseDecision' = "Abort"   
    /\ UNCHANGED << transactionStatus, votingPhaseConsensus, failureDuringVotingPhase >>

CompleteTransaction ==
    /\ transactionStatus = "InProgress"
    /\ commitPhaseDecision # "Waiting"
    /\ \/ /\ commitPhaseDecision = "Commit"
          /\ transactionStatus' = "Commited"
       \/ /\ commitPhaseDecision = "Abort"
          /\ transactionStatus' = "Aborted"
    /\ UNCHANGED << failureDuringVotingPhase, votingPhaseConsensus, commitPhaseDecision >>

Complete ==
    /\ transactionStatus # "InProgress"
    /\ UNCHANGED vars

---------

Init ==
    /\ failureDuringVotingPhase = FALSE
    /\ votingPhaseConsensus = "NotAvailable"
    /\ commitPhaseDecision = "Waiting"
    /\ transactionStatus = "InProgress"
    

Next ==
    \/ ProcessVotingPhase
    \/ ProcessCommitPhase
    \/ CompleteTransaction
    \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------

VotingCrashLeadsToAbort ==
    (votingPhaseConsensus = "NotAvailable" /\ transactionStatus = "Aborted")
        => failureDuringVotingPhase 

IInv ==
  /\ transactionStatus = "Aborted" => commitPhaseDecision = "Abort"
  /\ \/ commitPhaseDecision = "Abort" =>
        \/ votingPhaseConsensus = "No"
        \/ votingPhaseConsensus = "NotAvailable"
     \/ commitPhaseDecision = "Commit" =>
        /\ votingPhaseConsensus = "Yes"
  /\ votingPhaseConsensus = "NotAvailable" =>
        \/ failureDuringVotingPhase = TRUE
        \/ commitPhaseDecision = "Waiting"

THEOREM Spec_VotingCrashLeadsToAbort ==
    Spec => []VotingCrashLeadsToAbort
PROOF
    <1>1. Init => IInv BY DEF Init, IInv
    <1>2. IInv /\ [Next]_vars => IInv'
        <2> SUFFICES ASSUME IInv, Next PROVE IInv /\ Next => IInv'
        <2>1. ASSUME IInv, ProcessVotingPhase
              PROVE (IInv /\ ProcessVotingPhase) => IInv'
              BY VotingPhaseConsensusesAssume DEF IInv, ProcessVotingPhase, FailCoordinator, DetermineVoterConsensus
        <2>2. ASSUME IInv, ProcessCommitPhase
              PROVE (IInv /\ ProcessCommitPhase) => IInv'
              BY CommitPhaseDecisionsAssume DEF IInv, ProcessCommitPhase
        <2>3. ASSUME IInv, CompleteTransaction
              PROVE (IInv /\ CompleteTransaction) => IInv'
              BY TransactionStatusesAssume DEF IInv, CompleteTransaction
        <2>4. ASSUME IInv, Complete
              PROVE (IInv /\ Complete) => IInv' 
              OMITTED
        <2>q. QED BY <2>1, <2>2, <2>3, <2>4 DEF Next      
    <1>3. IInv => VotingCrashLeadsToAbort BY DEF IInv, VotingCrashLeadsToAbort
    <1>q. QED BY PTL, <1>1, <1>2, <1>3 DEF Spec
====