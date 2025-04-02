---- MODULE 2PC_abs ----

CONSTANT Sites
CONSTANT VotingPhaseConsensuses
CONSTANT CommitPhaseDecisions
CONSTANT TransactionStatuses

VARIABLE votingPhaseConsensus
VARIABLE commitPhaseDecision
VARIABLE transactionStatus
VARIABLE failureDuringVotingPhase

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
    /\ IF votingPhaseConsensus = "Yes"
            THEN commitPhaseDecision' = "Commit"
       ELSE commitPhaseDecision' = "Abort"   
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

====