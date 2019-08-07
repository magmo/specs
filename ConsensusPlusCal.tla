-------------------------- MODULE ConsensusPlusCal --------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS
    Names,
    PossibleAllocations,
    Participants,
    Allocations,
    NULL
ASSUME Len(Participants) = Len(Allocations)

NumParticipants == Len(Participants)

            
(* --algorithm consensus_update

\* For the moment, we assume that participants only send commitments forward.
\* Since messages are read and then discarded, it's enough to just store one.
variables msg = NULL


define
ourTurn == TRUE
allocationOk == TRUE
end define;


fair process updateConsensus \in DOMAIN Participants
variable
  state = [allocation |-> Allocations[self], turnNumber |-> 1, type |-> "Waiting"],
  me = Participants[self]
begin
  \* Each participant atomically reads the message, updates their state,
  \* and sends a message if it's their turn, accordingly.
  \* We assume that messages that create invalid transitions are discarded.
  \* Therefore, every incoming message considered here is considered a source of truth.
  A:
    if
      /\ msg /= NULL
      /\ msg.to = me
      /\ msg.turnNumber > state.turnNumber 
    then
        \* First, update our state based on the incoming message
        if msg.furtherVotesRequired = 0
        then state := [type |-> "Success"];
        elsif ourTurn
        then
            if state.type = "Sent"
            then state := [type |-> "Failure"];
            elsif allocationOk
            then skip; \* TODO: Send vote
            else skip; \* TODO: Send reject
            end if;
        else
            state := [
                allocation |-> state.allocation,
                turnNumber |-> msg.turnNumber,
                type       |-> "Waiting"
            ];
        end if;
    end if;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES msg, pc

(* define statement *)
ourTurn == TRUE
allocationOk == TRUE

VARIABLES state, me

vars == << msg, pc, state, me >>

ProcSet == (DOMAIN Participants)

Init == (* Global variables *)
        /\ msg = NULL
        (* Process updateConsensus *)
        /\ state = [self \in DOMAIN Participants |-> [allocation |-> Allocations[self], turnNumber |-> 1, type |-> "Waiting"]]
        /\ me = [self \in DOMAIN Participants |-> Participants[self]]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ IF /\ msg /= NULL
                 /\ msg.to = me[self]
                 /\ msg.turnNumber > state[self].turnNumber
                 THEN /\ IF msg.furtherVotesRequired = 0
                            THEN /\ state' = [state EXCEPT ![self] = [type |-> "Success"]]
                            ELSE /\ IF ourTurn
                                       THEN /\ IF state[self].type = "Sent"
                                                  THEN /\ state' = [state EXCEPT ![self] = [type |-> "Failure"]]
                                                  ELSE /\ IF allocationOk
                                                             THEN /\ TRUE
                                                             ELSE /\ TRUE
                                                       /\ state' = state
                                       ELSE /\ state' = [state EXCEPT ![self] =          [
                                                                                    allocation |-> state[self].allocation,
                                                                                    turnNumber |-> msg.turnNumber,
                                                                                    type       |-> "Waiting"
                                                                                ]]
                 ELSE /\ TRUE
                      /\ state' = state
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << msg, me >>

updateConsensus(self) == A(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in DOMAIN Participants: updateConsensus(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DOMAIN Participants : WF_vars(updateConsensus(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


AllowedMessages ==
  [
    turnNumber: Nat,
    votesRequired : 0..(NumParticipants - 1),
    to: Names,
    allocation: PossibleAllocations
  ]
  \cup { NULL }

States == {} 
  \cup [allocation: PossibleAllocations, turnNumber: Nat, type: {"Waiting"}]
  \cup [allocation: PossibleAllocations, turnNumber: Nat, type: {"Sent"}, status: {"Voted", "Rejected"}]

TypeOK ==  
  /\ PrintT(<<msg, state>>) \* Debugging statement
  \* The following two conditions specify the format of each message and
  \* participant state
  /\ state \in [DOMAIN Participants -> States]
  /\ msg \in AllowedMessages

TurnNumberIncrements ==
  /\ \A p \in DOMAIN Participants: state'[p].turnNumber >= state[p].turnNumber

ProtocolTerminates == <>[](
  \A p \in DOMAIN Participants:
    \/ state[p].type = "Success"
    \/ state[p].type = "Failure"
)


=============================================================================
\* Modification History
\* Last modified Wed Aug 07 09:27:25 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
