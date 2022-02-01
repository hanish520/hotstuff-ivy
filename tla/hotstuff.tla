------------------------------ MODULE hotstuff ------------------------------
EXTENDS Integers, FiniteSets, Tree

(***************************************************************************)
(* Constants: CNodes correct nodes, FNodes faulty nodes                    *)
(***************************************************************************)
CONSTANT CNodes, FNodes, Quorums

Nodes == CNodes \cup FNodes

(***************************************************************************)
(* Quorum Assumption                                                       *)
(* - Quorums are sets of nodes                                             *)
(* - Two quorums intersect in a correct node                               *)
(* - The set of quorums is subset closed                                   *)
(* - The set of all nodes is a quorum                                      *)
(***************************************************************************)
ASSUME QuorumAssumption == 
            /\ \A Q \in Quorums : Q \subseteq Nodes
            /\ \A Q1, Q2 \in Quorums : \E n \in CNodes: n \in (Q1 \cap Q2)
            /\ \A Q \in Quorums: \A S \in SUBSET Nodes: 
                                Q \subseteq S => S \in Quorums
            /\ Nodes \in Quorums

(***************************************************************************)
(* votes stores the votes for every block, i.e.  which node has signed a   *)
(* block.                                                                  *)
(* lock is the locked block for every node                                 *)
(* max is the max signed block for every node                              *)
(***************************************************************************)
VARIABLE votes, lock, max

vars == <<round, parent, votes, lock, max>>

TypeOK == /\ round \in [Blocks -> Rounds]
          /\ parent \in [Blocks -> Blocks]
          /\ votes \in [Blocks -> SUBSET Nodes]
          /\ lock \in [Nodes -> Blocks]
          /\ max \in [Nodes -> Rounds]

(***************************************************************************)
(* Initially all blocks but genesis have round -1.                         *)
(* All blocks are their own parent.                                        *)
(* No block is voted for, except genesis.                                  *)
(* All nodes voted for the genesis block.                                  *)
(***************************************************************************)

Init == /\ lock = [n \in Nodes |-> gen]
        /\ max = [n \in Nodes |-> 0]
        /\ round = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
        /\ parent = [b \in Blocks |-> b]
        /\ votes = [[b \in Blocks |-> {}] EXCEPT ![gen]=Nodes]

(***************************************************************************)
(* A proposed block is a block in the tree, i.e. round > -1                *)
(***************************************************************************)
Proposed(b) == /\ b \in Blocks
               /\ round[b] /= -1

(***************************************************************************)
(* A block is confirmed if a quorum of nodes voted for the block,          *)
(* i.e. it has a certificate.                                              *)
(***************************************************************************)
Confirmed(b) == /\ Proposed(b)
                /\ votes[b] \in Quorums
 
(***************************************************************************)
(* The propose action adds a new block to the tree.                        *)
(* The parent must be confirmed,                                           *)
(* the new block gets a round larger than that of his parent.              *)
(***************************************************************************)
propose(b,p,r) == /\ round' = [round EXCEPT ![b] = r]
                  /\ parent' = [parent EXCEPT ![b] = p]
        
Propose(b,p,r) == /\ b \in Blocks 
                  /\ ~ Proposed(b)
                  /\ Confirmed(p)
                  /\ r > round[p]
                  /\ propose(b,p,r)
                  /\ UNCHANGED <<lock, max, votes>>

(***************************************************************************)
(* Vote models one node voting (or signing) a block.                       *)
(* The max and lock variables for the node are adjusted.                   *)
(***************************************************************************)
vote(n,b) == /\ max' = [max EXCEPT ![n] = round[b]]
             /\ votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
             /\ IF round[parent[parent[b]]] > round[lock[n]]
                    (*******************************************************)
                    (* If the grandbarent of the new signed block has a    *)
                    (* larger round than the current lock, the lock is     *)
                    (* updated.                                            *)
                    (*******************************************************) 
                    THEN lock' = [lock EXCEPT ![n] = parent[parent[b]]]
                ELSE lock' = lock  

Vote(n,b) == /\ Proposed(b)
             /\ n \in Nodes
             /\ \/ n \notin CNodes
                (***********************************************************)
                (* Below are the rules on signing, but they apply only to  *)
                (* correct nodes.                                          *)
                (***********************************************************)
                \/ /\ round[b] > max[n]
                   (********************************************************)
                   (* Below is the updated rule for simplified hotstuff.   *)
                   (********************************************************) 
                   /\ round[lock[n]] <= round[parent[b]]
                   (********************************************************)
                   (* The rule from original hotstuff includes the         *)
                   (* Ancestor predicate.                                  *)
                   (********************************************************)
                   \* /\ \/ Ancestor(lock[n],b) \* safety rule 
                   \*    \/ round[lock[n]] < round[parent[b]] \* lifeness rule
             /\ vote(n,b)
             /\ UNCHANGED <<round, parent>>

(***************************************************************************)
(* Chain specifies that blocks from b to c form a 2-chain                  *)
(***************************************************************************)
chain(b,c) == /\ parent[parent[c]] = b
              /\ round[c] <= round[parent[c]] + 1
              /\ round[parent[c]] <= round[b] + 1

(***************************************************************************)
(* A block is committed if it is the start of a 2-chain, and the last node *)
(* in the 2-chain is confirmed.                                            *)
(***************************************************************************)                      
Committed(b) == \/ \E c \in Blocks:
                   /\ chain(b,c)
                   /\ Confirmed(c)
                \/ b = gen

(***************************************************************************)
(* Stop models the stopping of the node and resets the max and lock        *)
(***************************************************************************)
Stop(n) == /\ lock' = [lock EXCEPT ![n] = gen]
           /\ max' = [max EXCEPT ![n] = 0]
           /\ UNCHANGED <<round, parent, votes>>

(****************************************************************************)
(* Start models the adding of the node in to the cluster                    *)
(****************************************************************************)
Start(n) == /\ LET maxCommitedBlock == CHOOSE b \in Blocks:
                                   /\ \A bk \in {bb \in Blocks: Committed(bb)}:
                                                    round[b] \geq round[bk]
                                   /\ Committed(b)
               IN lock' = [lock EXCEPT ![n] = maxCommitedBlock]
            /\ UNCHANGED <<round, parent, votes, max>>
          
Next == \/ \E b,p \in Blocks: \E r \in Rounds: Propose(b,p,r)
        \/ \E b \in Blocks: \E n \in Nodes: Vote(n,b)
        \/ \E n \in Nodes: Stop(n) /\ Start(n)
        
Spec == Init /\ [][Next]_vars
                      
               
(***************************************************************************)
(* Correct, is the main safety property.                                   *)
(* It shows that, for committed b, at rounds larger than b,                *)
(* only descendants of b can be confirmed.                                 *)
(*                                                                         *)
(* We prove Correct, by proving that iCorrect holds for all i,             *)
(* using induction over i.                                                 *)
(***************************************************************************)
cci(b,c,i) == /\ Committed(b)
              /\ Confirmed(c)
              /\ round[b] + i = round[c]
        
iCorrect(i) == \A b, c \in Blocks: 
               cci(b,c,i)
               => Ancestor(b,c)

cc(b,c) == /\ Committed(b)
           /\ Confirmed(c)
           /\ round[b] <= round[c]
            
Correct ==  \A b, c \in Blocks: 
               cc(b,c)
               => Ancestor(b,c)           
               
Safe == \A b,c \in Blocks: Committed(b) /\ Committed(c) 
                        => Ancestor(c,b) \/ Ancestor(b,c)

=============================================================================
\* Modification History
\* Last modified Fri Jan 28 11:39:26 CET 2022 by 2924108
\* Created Wed Jan 26 13:43:46 CET 2022 by 2924108
