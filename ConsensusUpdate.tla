-------------------------- MODULE ConsensusUpdate --------------------------
EXTENDS Integers, Sequences, TLC
CONSTANTS
    Names, \* a set
    Participants, \* an array of participants, in their order in the state channel
    NULL
ASSUME
  /\ Len(Participants) > 1

NumParticipants == Len(Participants)
Types == [
    WAITING |-> "WAITING",
    SENT    |-> "SENT",
    SUCCESS |-> "SUCCESS",
    FAILURE |-> "FAILURE"
]
Status == [
  OK        |-> "OK",
  ABORT     |-> "ABORT",
  SUCCESS   |-> "SUCCESS"
]

Range(f) == { f[x] : x \in DOMAIN f }
Running(state) == state.type \in { Types.WAITING, Types.SENT }
Terminated(state) == ~Running(state)
            
(* --algorithm consensus_update

variables msgs = [p \in Names |-> {}]

define
\* Arrays are 1-indexed, while the % operator returns a number between 0 and NumParticipants.
\* This explains the following slightly complicated expression
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
currentlyOurTurn(state) ==
    /\ state.type = Types.WAITING
    /\ state.ourIndex = mover(state.turnNumber)
becomesOurTurn(state, msg) ==
   /\ state.type = Types.WAITING
   /\ msg.status = Status.OK
   /\ state.ourIndex = mover(msg.turnNumber)

target(turnNumber) == Participants[mover(turnNumber)]
end define;

macro pushMsg(m, sender)
begin
msgs := [recipient \in Names |-> IF recipient = sender THEN msgs[recipient] ELSE msgs[recipient] \cup {m}];
end macro;

macro sendVote(turnNumber, votesRequired, me)
begin
assert votesRequired > 0;
state := [
    type |-> Types.SENT,
    turnNumber |-> turnNumber,
    ourIndex   |-> state.ourIndex
];
pushMsg([
    turnNumber      |-> state.turnNumber,
    votesRequired   |-> votesRequired,
    status          |-> Status.OK
], me)
end macro;


macro returnSuccess(me)
begin
state := [ type |-> Types.SUCCESS] @@ state;
pushMsg([status |-> Status.SUCCESS], me)
end macro;

macro returnFailure(turnNumber, me)
begin
state := [
    type |-> Types.FAILURE,
    turnNumber |-> turnNumber
] @@ state;
pushMsg([
    status |-> Status.ABORT
], me);
end macro;
 
macro vote(turnNumber, votesRequired)
begin
if votesRequired = 0 then returnSuccess(me)
else sendVote(turnNumber, votesRequired, me)
end if; end macro;

macro waitForUpdate(turnNumber, me)
begin
state := [
    turnNumber |-> msg.turnNumber,
    type       |-> Types.WAITING,
    ourIndex   |-> state.ourIndex
];
msgs[me] := msgs[me] \ {msg};
end macro;

(***************************************************************************)
(* Calling this a fair process prevents the process from stuttering        *)
(* forever.  It's always considered to be valid to take a step where your  *)
(* state variables don't change, which could be the case if some unrelated *)
(* protocols end up in an infinite loop, for instance.  However, we want   *)
(* to check that IF A: wallets always eventually take some valid action    *)
(* THEN B: wallets always eventually terminate the consensus-update        *)
(* protocol Calling the process fair ensures that A is true, and therefore *)
(* the model checks that under the assumption A, B is also true.           *)
(***************************************************************************)
fair process consensusUpdate \in DOMAIN Participants
variables
  state = [
    turnNumber |-> 1,
    ourIndex |-> self,
    type |-> Types.WAITING
  ],
  me = Participants[self],
  msg = NULL

begin
  (*************************************************************************)
  (*    Each participant either                                            *)
  (*   A. sends a message if it's currently safe to do                     *)
  (*  so, or else                                                          *)
  (*   B. it reads a message for the participant, updates their            *)
  (* state accordingly and sends a message if it's then safe, then removes *)
  (* the message from their inbox.                                         *)
  (*                                                                       *)
  (* In the case B, these three actions are currently assumed to be        *)
  (* atomic, and are therefore assigned to a single label,                 *)
  (* `ReachConsensus`                                                      *)
  (*************************************************************************)
  ReachConsensus:
    while Running(state) do
        if currentlyOurTurn(state) then
            if state.type = Types.WAITING then vote(state.turnNumber+1, NumParticipants - 1);
            elsif state.type = Types.SENT then returnFailure(state.turnNumber, me);
            else assert FALSE
            end if;
        else
        ReadMessage: 
            with m \in msgs[me] do msg := m end with;
        ProcessMessage:
            \* If the commitment receved is not valid, return FAILURE
            \* TODO: Is this the actual behaviour we want?
            \* In the readme, we say this is what works, but the reducer does not
            \* work this way
            either returnFailure(state.turnNumber, me)
            \* In this case, the commitment was valid.
            or if msg.status = Status.OK then
                if msg.turnNumber > state.turnNumber then
                    \* First, update our state based on the incoming message
                    if msg.votesRequired = 0 then returnSuccess(me)
                    elsif becomesOurTurn(state, msg) then \* TODO: This should check if we're moving after receiving msg
                        if    state.type = Types.SENT then returnFailure(msg.turnNumber, me)
                        elsif state.type = Types.WAITING then vote(msg.turnNumber + 1, msg.votesRequired - 1)
                        else assert FALSE;
                        end if;
                    else
                        waitForUpdate(msg, me);
                    end if;
                end if;
            elsif msg.status = Status.ABORT   then returnFailure(state.turnNumber, me)
            elsif msg.status = Status.SUCCESS then returnSuccess(me)
            end if; end either;
        RemoveMessage:
            msgs[self] := msgs[self] \ {msg};
            msg := NULL;
        end if;

    end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES msgs, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
currentlyOurTurn(state) ==
    /\ state.type = Types.WAITING
    /\ state.ourIndex = mover(state.turnNumber)
becomesOurTurn(state, msg) ==
   /\ state.type = Types.WAITING
   /\ msg.status = Status.OK
   /\ state.ourIndex = mover(msg.turnNumber)







target(turnNumber) == Participants[mover(turnNumber)]

VARIABLES state, me, msg

vars == << msgs, pc, state, me, msg >>

ProcSet == (DOMAIN Participants)

Init == (* Global variables *)
        /\ msgs = [p \in Names |-> {}]
        (* Process consensusUpdate *)
        /\ state = [self \in DOMAIN Participants |->         [
                                                       turnNumber |-> 1,
                                                       ourIndex |-> self,
                                                       type |-> Types.WAITING
                                                     ]]
        /\ me = [self \in DOMAIN Participants |-> Participants[self]]
        /\ msg = [self \in DOMAIN Participants |-> NULL]
        /\ pc = [self \in ProcSet |-> "ReachConsensus"]

ReachConsensus(self) == /\ pc[self] = "ReachConsensus"
                        /\ IF Running(state[self])
                              THEN /\ IF currentlyOurTurn(state[self])
                                         THEN /\ IF state[self].type = Types.WAITING
                                                    THEN /\ IF (NumParticipants - 1) = 0
                                                               THEN /\ state' = [state EXCEPT ![self] = [ type |-> Types.SUCCESS] @@ state[self]]
                                                                    /\ IF msg[self] = NULL
                                                                          THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                          ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                    /\ msg' = [msg EXCEPT ![self] = NULL]
                                                               ELSE /\ Assert((NumParticipants - 1) > 0, 
                                                                              "Failure of assertion at line 66, column 1 of macro called at line 144, column 48.")
                                                                    /\ state' = [state EXCEPT ![self] =          [
                                                                                                            type |-> Types.SENT,
                                                                                                            turnNumber |-> (state[self].turnNumber+1),
                                                                                                            ourIndex   |-> state[self].ourIndex
                                                                                                        ]]
                                                                    /\ IF msg[self] = NULL
                                                                          THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                                                              turnNumber      |-> state'[self].turnNumber,
                                                                                              votesRequired   |-> (NumParticipants - 1),
                                                                                              status          |-> Status.OK
                                                                                          ])}]
                                                                          ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                                                              turnNumber      |-> state'[self].turnNumber,
                                                                                              votesRequired   |-> (NumParticipants - 1),
                                                                                              status          |-> Status.OK
                                                                                          ])}]
                                                                    /\ msg' = [msg EXCEPT ![self] = NULL]
                                                    ELSE /\ IF state[self].type = Types.SENT
                                                               THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                            type |-> Types.FAILURE,
                                                                                                            turnNumber |-> (state[self].turnNumber)
                                                                                                        ] @@ state[self]]
                                                                    /\ IF msg[self] = NULL
                                                                          THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                                                              status |-> Status.ABORT
                                                                                          ])}]
                                                                          ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                                                              status |-> Status.ABORT
                                                                                          ])}]
                                                                    /\ msg' = [msg EXCEPT ![self] = NULL]
                                                               ELSE /\ Assert(FALSE, 
                                                                              "Failure of assertion at line 146, column 18.")
                                                                    /\ UNCHANGED << msgs, 
                                                                                    state, 
                                                                                    msg >>
                                              /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "ReadMessage"]
                                              /\ UNCHANGED << msgs, state, msg >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << msgs, state, msg >>
                        /\ me' = me

ReadMessage(self) == /\ pc[self] = "ReadMessage"
                     /\ \E m \in msgs[me[self]]:
                          msg' = [msg EXCEPT ![self] = m]
                     /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                     /\ UNCHANGED << msgs, state, me >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ \/ /\ state' = [state EXCEPT ![self] =          [
                                                                      type |-> Types.FAILURE,
                                                                      turnNumber |-> (state[self].turnNumber)
                                                                  ] @@ state[self]]
                              /\ IF msg[self] = NULL
                                    THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                        status |-> Status.ABORT
                                                    ])}]
                                    ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                        status |-> Status.ABORT
                                                    ])}]
                              /\ msg' = [msg EXCEPT ![self] = NULL]
                           \/ /\ IF msg[self].status = Status.OK
                                    THEN /\ IF msg[self].turnNumber > state[self].turnNumber
                                               THEN /\ IF msg[self].votesRequired = 0
                                                          THEN /\ state' = [state EXCEPT ![self] = [ type |-> Types.SUCCESS] @@ state[self]]
                                                               /\ IF msg[self] = NULL
                                                                     THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                     ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                               /\ msg' = [msg EXCEPT ![self] = NULL]
                                                          ELSE /\ IF becomesOurTurn(state[self], msg[self])
                                                                     THEN /\ IF state[self].type = Types.SENT
                                                                                THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                                                             type |-> Types.FAILURE,
                                                                                                                             turnNumber |-> (msg[self].turnNumber)
                                                                                                                         ] @@ state[self]]
                                                                                     /\ IF msg[self] = NULL
                                                                                           THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                                                                               status |-> Status.ABORT
                                                                                                           ])}]
                                                                                           ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                                                                               status |-> Status.ABORT
                                                                                                           ])}]
                                                                                     /\ msg' = [msg EXCEPT ![self] = NULL]
                                                                                ELSE /\ IF state[self].type = Types.WAITING
                                                                                           THEN /\ IF (msg[self].votesRequired - 1) = 0
                                                                                                      THEN /\ state' = [state EXCEPT ![self] = [ type |-> Types.SUCCESS] @@ state[self]]
                                                                                                           /\ IF msg[self] = NULL
                                                                                                                 THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                                                                 ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                                                           /\ msg' = [msg EXCEPT ![self] = NULL]
                                                                                                      ELSE /\ Assert((msg[self].votesRequired - 1) > 0, 
                                                                                                                     "Failure of assertion at line 66, column 1 of macro called at line 164, column 63.")
                                                                                                           /\ state' = [state EXCEPT ![self] =          [
                                                                                                                                                   type |-> Types.SENT,
                                                                                                                                                   turnNumber |-> (msg[self].turnNumber + 1),
                                                                                                                                                   ourIndex   |-> state[self].ourIndex
                                                                                                                                               ]]
                                                                                                           /\ IF msg[self] = NULL
                                                                                                                 THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                                                                                                     turnNumber      |-> state'[self].turnNumber,
                                                                                                                                     votesRequired   |-> (msg[self].votesRequired - 1),
                                                                                                                                     status          |-> Status.OK
                                                                                                                                 ])}]
                                                                                                                 ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                                                                                                     turnNumber      |-> state'[self].turnNumber,
                                                                                                                                     votesRequired   |-> (msg[self].votesRequired - 1),
                                                                                                                                     status          |-> Status.OK
                                                                                                                                 ])}]
                                                                                                           /\ msg' = [msg EXCEPT ![self] = NULL]
                                                                                           ELSE /\ Assert(FALSE, 
                                                                                                          "Failure of assertion at line 165, column 30.")
                                                                                                /\ UNCHANGED << msgs, 
                                                                                                                state, 
                                                                                                                msg >>
                                                                     ELSE /\ state' = [state EXCEPT ![self] =          [
                                                                                                                  turnNumber |-> msg[self].turnNumber,
                                                                                                                  type       |-> Types.WAITING,
                                                                                                                  ourIndex   |-> state[self].ourIndex
                                                                                                              ]]
                                                                          /\ msgs' = [msgs EXCEPT ![me[self]] = msgs[me[self]] \ {msg[self]}]
                                                                          /\ msg' = msg
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED << msgs, 
                                                                    state, msg >>
                                    ELSE /\ IF msg[self].status = Status.ABORT
                                               THEN /\ state' = [state EXCEPT ![self] =          [
                                                                                            type |-> Types.FAILURE,
                                                                                            turnNumber |-> (state[self].turnNumber)
                                                                                        ] @@ state[self]]
                                                    /\ IF msg[self] = NULL
                                                          THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {(        [
                                                                              status |-> Status.ABORT
                                                                          ])}]
                                                          ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {(        [
                                                                              status |-> Status.ABORT
                                                                          ])}]
                                                    /\ msg' = [msg EXCEPT ![self] = NULL]
                                               ELSE /\ IF msg[self].status = Status.SUCCESS
                                                          THEN /\ state' = [state EXCEPT ![self] = [ type |-> Types.SUCCESS] @@ state[self]]
                                                               /\ IF msg[self] = NULL
                                                                     THEN /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                                     ELSE /\ msgs' = [recipient \in Names |-> IF recipient = me[self] THEN msgs[recipient] \ {msg[self]} ELSE msgs[recipient] \cup {([status |-> Status.SUCCESS])}]
                                                               /\ msg' = [msg EXCEPT ![self] = NULL]
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED << msgs, 
                                                                               state, 
                                                                               msg >>
                        /\ pc' = [pc EXCEPT ![self] = "ReachConsensus"]
                        /\ me' = me

consensusUpdate(self) == ReachConsensus(self) \/ ReadMessage(self)
                            \/ ProcessMessage(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in DOMAIN Participants: consensusUpdate(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DOMAIN Participants : WF_vars(consensusUpdate(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedMessages ==
  [
    turnNumber: Nat,
    votesRequired : 0..(NumParticipants - 1),
    status: { Status.OK }
  ]
  \cup [
    status: { Status.ABORT, Status.SUCCESS }
  ]

States == {} 
  \cup [turnNumber: Nat, ourIndex: DOMAIN Participants, type: Range(Types)]

\* Safety properties

TypeOK ==
  \* The following two conditions specify the format of each message and
  \* participant state.
  /\ state \in [DOMAIN Participants -> States]
  /\ \A p \in Names : \A m \in msgs[p] : msg \in AllowedMessages

\* TODO: Get TurnNumberDoesNotDecrease and StaysTerminated
\* For some reason, state[p].turnNumber' is not valid
TurnNumberDoesNotDecrease ==
  /\ \A p \in DOMAIN Participants: state[p].turnNumber' >= state[p].turnNumber

\* Once a process has terminated, its state does not change.
StaysTerminated == \A p \in DOMAIN Participants: (Terminated(state[p]) => (state'[p] = state[p]))
  
\* Liveness properties

\* The protocol always terminates consistently across all processes.
\* TODO: Is this actually feasible, or actually what we want?
\* For example, perhaps the last person to vote agrees, and sends a message reaching consensus.
\* Their process terminates in the SUCCESS state, but for whatever reason their
\* commitment was invalid, and the other processes therefore terminate in FAILURE.
ProtocolTerminates == 
    \/ /\ (\A p \in DOMAIN Participants: <>[](state[p].type = Types.SUCCESS))
       /\ TRUE \* TODO: In this case, should we specify that they reach the same turn number?
    \/ (\A p \in DOMAIN Participants: <>[](state[p].type = Types.FAILURE))
    
\* The value of msg should eventually always be NULL
MessagesAreRead == <>[](msgs = [p \in DOMAIN Participants |-> {"Foo"}])

=============================================================================
\* Modification History
\* Last modified Thu Aug 15 17:26:31 PDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
