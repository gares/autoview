From mathcomp Require Import all_ssreflect.

Module Problem.

Lemma tedius b1 b2 b3 b4 :
  [&& b1, b2, b3 & b4] = true -> b3 = true.
Proof.
move=> /andP[p1 /andP[p2 /andP[p3 p4]]].
by [].
(* move=> /and4P[p1 p2 p3 p4]. *)
Qed.

Lemma tedius2 b1 b2 b3 :
  b1 && b2 || b3 -> b3 || b1.
Proof.
move=> /orP[/andP[p1 p2]|p3].
  by rewrite p1 orbC.
by rewrite p3.
Qed.

End Problem.


Module FirstAttempt.

Class View (p : Prop) (b : bool) :=
  { r : reflect p b }.

Lemma xP b p {v : View p b} : reflect p b.
Proof. by apply r. Qed.
  
Instance andV4 (p1 p2 p3 p4 : bool) :
   View [/\ p1, p2, p3 & p4] [&& p1, p2, p3 & p4] | 80.
Proof. by split; apply: and4P. Qed.

Instance andV (p1 p2 : bool) :
   View (p1 /\ p2) (p1 && p2) | 90.
Proof. by split; apply: andP. Qed.

Lemma tedius b1 b2 b3 b4 :
  [&& b1, b2, b3 & b4] = true -> b3 = true.
Proof.
move=> /andP[_ /andP[_]]. move=> /xP.
Admitted.

End FirstAttempt.

(* merit *)

Module Recursion.

Class RView (p : Prop) (b : bool) :=
  { r : reflect p b }.

Lemma rxP b p {v : RView p b} : reflect p b.
Proof. by apply r. Qed.
  
Instance andV p1 p2 q1 q2 :
   RView q1 p1 -> RView q2 p2 ->
   RView (q1 /\ q2) (p1 && p2) | 90.
Proof.
move=> [v1] [v2]; split.
by apply: (iffP andP) => -[] /v1 ? /v2 ?; split.
Qed.

Instance orV p1 p2 q1 q2 :
   RView q1 p1 -> RView q2 p2 ->
   RView (q1 \/ q2) (p1 || p2) | 90.
Proof.
move=> [v1] [v2]; split.
apply: (iffP orP) => -[ /v1 | /v2 ] ?; by [left|right].
Qed.

Instance idV (b : bool) : RView b b | 99.
Proof. by split; apply: idP. Qed.

Lemma tedius2 b1 b2 b3 :
  b1 && b2 || b3 -> b3 || b1.
Proof.
move=> /rxP.
Admitted.

End Recursion.

Module UsabilityIssues.
Import Recursion.

Check (rxP (true && false) _).
Check (rxP _ (true /\ false)).

Hint Mode RView + - : typeclass_instances.
Hint Mode RView - + : typeclass_instances.

Check (rxP _ _).

End UsabilityIssues.


Module OneView.

(* not an inductive *)

Definition vlevel := unit.

Definition vRec : vlevel. Proof. by []. Qed.
Definition vBase : vlevel. Proof. by []. Qed. 
Definition vStop : vlevel. Proof. by []. Qed. 

Class View (l : vlevel) (p : Prop) (b : bool) :=
  { r : reflect p b }.

Lemma x_many_P l b p {v : View l p b} : reflect p b.
Proof. by apply r. Qed.

Notation xP  := (x_many_P vBase).
Notation rxP := (x_many_P vRec). 

Class Valid (current : vlevel) (next : vlevel).
Instance r1 : Valid vBase vStop.
Instance r2 : Valid vRec vRec    | 90.
Instance r3 : Valid vRec vStop   | 99.

Instance andV l1a l1b l2 p1 p2 q1 q2
   {r1 : Valid l2 l1a} {r2 : Valid l2 l1b} :
   View l1a q1 p1 -> View l1b q2 p2 ->
   View l2 (q1 /\ q2) (p1 && p2) | 90.
Proof.
move=> [v1] [v2]; split.
by apply: (iffP andP) => -[] /v1 ? /v2 ?; split.
Qed.

Instance orV l1a l1b l2 p1 p2 q1 q2
   {r1 : Valid l2 l1a} {r2 : Valid l2 l1b} :
   View l1a q1 p1 -> View l1b q2 p2 ->
   View l2 (q1 \/ q2) (p1 || p2) | 90.
Proof.
move=> [v1] [v2]; split.
apply: (iffP orP) => -[ /v1 | /v2 ] ?; by [left|right].
Qed.

Instance idV (b : bool) : View vStop b b | 99.
Proof. by split; apply: idP. Qed.

Hint Mode View + + - : typeclass_instances.
Hint Mode View + - + : typeclass_instances.

Lemma tedius2 b1 b2 b3 :
  b1 && b2 || b3 -> b3 || b1.
Proof.
move=> /xP. 
Admitted.

End OneView.

Module TheGameIsOn.

(* View level                                                           *)

Definition vlevel := unit.

Definition vL0 : vlevel. done. Qed.
Definition vOL : vlevel. done. Qed.   (* Only Logical *)
Definition vAC : vlevel. done. Qed.   (* All Core     *)
Definition vAL : vlevel. done. Qed.   (* All          *)
Definition vAB : vlevel. done. Qed.   (* All + under binder *)
Definition vL1 : vlevel. done. Qed.   (* All rules but no recursion *)

Class View (lv:vlevel) (p : Prop) (b : bool) := { r : reflect p b }.
Hint Mode View + + - : typeclass_instances.
Hint Mode View + - + : typeclass_instances.

Lemma xPm lv b p {v : View lv p b} : reflect p b.
Proof. by apply r. Qed.

Definition xP   := @xPm vL1.
Definition lxP  := @xPm vOL.
Definition rcxP := @xPm vAC.
Definition rxP  := @xPm vAL.
Definition rbxP := @xPm vAB.

(* -------------------------------------------------------------------- *)
(* Rule level                                                           *)
Definition rlevel := unit.
Definition rL0  : rlevel. done. Qed.   
Definition rOL  : rlevel. done. Qed. (* Only Logical *) 
Definition rOLr : rlevel. done. Qed. (* Only Logical but recursive like andP3 *) 
Definition rAC  : rlevel. done. Qed.
Definition rAL  : rlevel. done. Qed.
 
(* -------------------------------------------------------------------- *)
(* Valid rl vl                                                          *)
(* indicate if a rule at level rl can be used at the view level vl      *)
(* -------------------------------------------------------------------- *)

Class Valid (rl:rlevel) (vl:vlevel).
  Instance V_rL0 vl : Valid rL0 vl | 0.
  (* For level 1 *)
  Instance V_OL_L1  : Valid rOL vL1 | 0.
  Instance V_AC_L1  : Valid rAC vL1 | 0.
  Instance V_AL_L1  : Valid rAL vL1 | 0.
 
  (* For Only Logical *)
  Instance V_OL_OL  : Valid rOL  vOL | 0.
  Instance V_OLr_OL : Valid rOLr vOL | 0.

  (* For All Core *)
  Instance V_OL_AC rl `{Valid rl vOL} : Valid rl  vAC | 1.
  Instance V_AC_AC                    : Valid rAC vAC | 0.

  (* For All  and All bind *)
  Instance V_AC_AL rl : Valid rl vAL.
  Instance V_AL_AB rl : Valid rl vAB.

(* -------------------------------------------------------------------- *)
(* ArgRec vl avl                                                        *)
(* compute the view level avl of an argument of a logic rule used with  *)
(* view level vl                                                        *)
(* -------------------------------------------------------------------- *)

Class ArgRec (vl:vlevel) (avl:vlevel).
(* Hint Mode ArgRec + -. *)

Instance ArgRec_L1     : ArgRec vL1 vL0 | 0.
Instance ArgRec_dft vl : ArgRec vl  vl  | 1.

Class ArgBind (vl:vlevel) (avl:vlevel).
(* Hint Mode ArgBind + -. *)

Instance ArgBind_AB     : ArgBind vAB vAB | 0.
Instance ArgBind_dft vl : ArgBind vl  vL0  | 1.

(* -------------------------------------------------------------------- *)
(* Level 0 rules                                                        *)
Instance idV vl (b:bool) : View vl (is_true b) b | 100.
Proof. by split;apply idP. Qed.

(* -------------------------------------------------------------------- *)
(* Logical Rules                                                        *)
Instance negV vl avl `{Valid rOL vl} p b 
  `{ArgRec vl avl} `{View avl p b} : View vl (~p) (~~b) | 90.
Proof. by split; apply: (iffP negP) => HH /xPm. Qed.

Instance andV vl avl `{Valid rOL vl} p1 p2 b1 b2 
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} : 
  View vl (p1 /\ p2) (b1 && b2) | 90.
Proof. by split; apply: (iffP andP) => -[] /xPm ? /xPm. Qed.

Instance orV vl avl `{Valid rOL vl} p1 p2 b1 b2 
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} : 
  View vl (p1 \/ p2) (b1 || b2) | 90.
Proof. by split; apply: (iffP orP)=> -[] /xPm;auto. Qed.

Instance impV vl avl `{Valid rOL vl} p1 p2 b1 b2 
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} : 
  View vl (p1 -> p2) (b1 ==> b2) | 90.
Proof. by split; apply: (iffP implyP)=> HH /xPm /HH /xPm. Qed.

(* -------------------------------------------------------------------- *)
(* Logical Recursive Rules                                              *)

Instance and3V vl avl `{Valid rOLr vl} p1 p2 p3 b1 b2 b3
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} `{View avl p3 b3} :
  View vl [/\ p1, p2 & p3] [&& b1, b2 & b3] | 80.
Proof. 
  by split; apply: (iffP and3P) => -[] /xPm ? /xPm ? /xPm;constructor.
Qed.

Instance and4V vl avl `{Valid rOLr vl} p1 p2 p3 p4 b1 b2 b3 b4
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} `{View avl p3 b3}
  `{View avl p4 b4} : View vl [/\ p1, p2, p3 & p4] [&& b1, b2, b3 & b4] | 70.
Proof. 
  by split; apply: (iffP and4P) => -[] /xPm ? /xPm ? /xPm ? /xPm;constructor.
Qed.

Instance and5V vl avl `{Valid rOLr vl} p1 p2 p3 p4 p5 b1 b2 b3 b4 b5 
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} `{View avl p3 b3}
  `{View avl p4 b4} `{View avl p5 b5} : 
   View vl [/\ p1, p2, p3, p4 & p5] [&& b1, b2, b3, b4 & b5] | 60.
Proof. 
  by split; apply: (iffP and5P) => -[] /xPm ? /xPm ? /xPm ? /xPm ? /xPm;constructor.
Qed.

Instance or3V vl avl `{Valid rOLr vl} p1 p2 p3 b1 b2 b3
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} `{View avl p3 b3} :
  View vl [\/ p1, p2 | p3] [|| b1, b2 | b3] | 80.
Proof. 
  split; apply: (iffP or3P)=> -[] /xPm ?;
   ((by constructor 1) || (by constructor 2) || (by constructor 3)).
Qed.

Instance or4V vl avl `{Valid rOLr vl} p1 p2 p3 p4 b1 b2 b3 b4
  `{ArgRec vl avl} `{View avl p1 b1} `{View avl p2 b2} `{View avl p3 b3}
  `{View avl p4 b4} : View vl [\/ p1, p2, p3 | p4] [|| b1, b2, b3 | b4] | 70.
Proof. 
  split; apply: (iffP or4P)=> -[] /xPm ?;
   ((by constructor 1) || (by constructor 2) 
   || (by constructor 3) || (by constructor 4)).
Qed.

(* -------------------------------------------------------------------- *)
(* All Core Rules                                                       *)

Instance eqV vl (T:eqType) (x y:T) `{Valid rAC vl} : 
  View vl (x = y) (x == y) | 0.
Proof. by split;apply eqP. Qed.  
(*Typeclasses Opaque is_true. *)

(* All Rules  *)   

Instance forallV vl avl `{Valid rAL vl} (T:finType) (P:T->Prop) (p:pred T) 
  `{ArgBind vl avl} (V:forall x, View avl (P x) (p x)) :
  View vl (forall x : T, P x) [forall x, p x] | 90.
Proof. split; apply: forallPP=> ?;apply /xPm. Qed.

Instance allV vl avl `{Valid rAL vl} (T:eqType) (P:T->Prop) (p:pred T) l
  `{ArgBind vl avl} (V:forall x, View avl (P x) (p x)) :
  View vl (forall x : T, x \in l -> P x) (all p l) | 90.
Proof. by split; apply: (iffP allP)=> X ? /X /xPm. Qed.

Instance hasV vl avl `{Valid rAL vl} (T:eqType) (P:T->Prop) (p:pred T) l
  `{ArgBind vl avl} (V:forall x, View avl (P x) (p x)) : 
  View vl (exists x, x \in l /\ P x) (has p l). 
Proof.
  by (split; apply: (iffP hasP)) => [[x Hin /xPm ?]|[x [Hin /xPm ?]]]; exists x.
Qed.


(* -------------------------------------------------------------------- *)

Lemma test1 (b1 b2:bool) : b1 && b2.
Proof. 
apply /xP. 
Abort.

Lemma test1 (n1 n2:nat) : n1 <= n2.
Proof. 
apply /xP.
Abort.



Lemma test2 (b1 b2:bool) : b1 && b2 && (b1 == b2).
Proof. 
apply /rcxP.
Abort.

Lemma test3 (b1 b2 b3: bool) : [&& b1, b2 & b3].
Proof.
apply /rbxP.
Abort.

Lemma test4 (b1 b2 b3: bool) : [&& b1, b2, b3 & b3].
Proof.
apply /lxP.
Abort.

Lemma test5 (b1 b2 b3: bool) : [&& b1, b2, b3 & b3].
Proof.
apply /xP.
Abort.

(*
Typeclasses Opaque leq.
*)

Lemma test6 l : 
  has [pred x : nat | 0 < x <= 7] l.
Proof.
 apply /rbxP.
Abort.

End TheGameIsOn.




(*

With Canonical Structures it is harder.

Record c1P (b:bool) := mk_c1P { c1b : bool; c1p : Prop; _ : reflect c1p c1b }.
Record c2P (b:bool) := mk_c2P { c2b : bool; c2p : Prop; _ : reflect c2p c2b }.
Record c3P (b:bool) := mk_c3P { c3b : bool; c3p : Prop; _ : reflect c3p c3b }.
Record c4P (b:bool) := mk_c4P { c4b : bool; c4p : Prop; _ : reflect c4p c4b }.

Record wrapped T := Wrap { unwrap : T }.

Definition wrap4 T e := @Wrap T e.
Definition wrap3 T e := @wrap4 T e.
Definition wrap2 T e := @wrap3 T e.
Definition wrap1 T e := @wrap2 T e.
Canonical wrap1.


Record canonicalP (b:bool) := mk_cP{
  cano_bool : wrapped bool; 
  cano_prop : wrapped Prop; 
  _ : reflect (unwrap cano_prop) (unwrap cano_bool);
}.

Program Canonical cc1P b (c:c1P b) := @mk_cP b (wrap1 c.(c1b)) (wrap1 c.(c1p)) _.
Next Obligation. by case c. Qed.

Program Canonical cc2P b (c:c2P b) := @mk_cP b (wrap2 c.(c2b)) (wrap2 c.(c2p)) _.
Next Obligation. by case c. Qed.

Program Canonical cc3P b (c:c3P b) := @mk_cP b (wrap3 c.(c3b)) (wrap3 c.(c3p)) _.
Next Obligation. by case c. Qed.

Program Canonical cc4P b (c:c4P b) := @mk_cP b (wrap4 c.(c4b)) (wrap4 c.(c4p)) _.
Next Obligation. by case c. Qed.


Lemma xPb b (c:canonicalP b) : reflect (unwrap (cano_prop c)) (unwrap (cano_bool c)).
Proof. by case c. Qed. 

Definition rxP := @xPb true.
Definition lxP := @xPb false.

Canonical cP_id mode (b:bool) := @mk_cP mode (Wrap b) (Wrap (is_true b)) (@idP b).

Notation ucb x := (unwrap (cano_bool x)).
Notation ucp x := (unwrap (cano_prop x)).

Lemma cP_and mode (b1 b2:canonicalP mode) : c4P mode. 
Proof.
  refine (@mk_c4P mode (ucb b1 && ucb b2) (ucp b1 /\ ucp b2) _).
  by apply:(iffP andP) => -[] /xPb ? /xPb.
Defined.
Canonical cP_and.

(*Lemma cP_and3 (b1 b2 b3:canonicalP) : c3P. 
Proof.
  refine (@mk_c3P ([&& ucb b1 , ucb b2 & ucb b3]) ([/\ ucp b1 , ucp b2 & ucp b3]) _).
  by apply:(iffP and3P) => -[] /xP ? /xP ? /xP.
Defined.
Canonical cP_and3.
*)
Lemma cP_imp mode (b1 b2:canonicalP mode) : c4P mode. 
Proof.
  refine (@mk_c4P mode (ucb b1 ==> ucb b2) (ucp b1 -> ucp b2) _).
  by apply:(iffP implyP)=> H /xPb /H ?;apply /xPb.
Defined.
Canonical cP_imp.

(*Lemma cP_and4 (b1 b2 b3 b4:canonicalP) : c2P. 
Proof.
  refine (@mk_c2P ([&& ucb b1 , ucb b2 & ucb b3]) ([/\ ucp b1 , ucp b2 & ucp b3]) _).
  by apply:(iffP and4P) => -[] /xP ? /xP ? /xP .
Defined.
Canonical cP_and3. *)


Program Canonical cP_has (T:eqType) (P:pred T) l := @mk_c1P true _ _ (@hasP T P l).

*)
