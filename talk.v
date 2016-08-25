From mathcomp Require Import all_ssreflect.

(** #<div class="slide vfill"># *)
(** 

#<center>#
** Boolean reflection via type classes
#</center>#

#<center>#
Benjamin Gregoire
Enrico Tassi
#</center>#

#<center>#
Coq Workshop 2016
#</center>#

*)
(** #</div># *)

(** ------------------------------------- *)

(** #<div class="slide vfill"># *)
(** ** Boolean reflection

 - Bool whenever possible
 - Prop still needed
 - solution: view mechanism

*)
(** #</div># *)

(** ------------------------------------- *)
(** #<div class="slide"># *)
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

(** #</div># *)
(** ------------------------------------- *)

(** #<div class="slide vfill"># *)
(** ** Idea

  - Many times the choice of right view is obvious
    (for the library designer)
  - [xP] a single view to rule them all

*)
(** #</div># *)
(** ------------------------------------- *)
(** #<div class="slide"># *)

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

(** #</div># *)
(** ------------------------------------- *)

(** #<div class="slide vfill"># *)
(** ** Merit

 - No change to the tactic language
 - Best view choice wired in
 - Extensible by the user
 - Recursive (not yet)

*)
(** #</div># *)
(** ------------------------------------- *)
(** #<div class="slide"># *)

Module Recursion.

Class RView (p : Prop) (b : bool) :=
  { r : reflect p b }.

Lemma rxP b p {v : RView p b} : reflect p b.
Proof. by apply r. Qed.
  
Instance idRV (b : bool) : RView b b | 99.
Proof. by split; apply: idP. Qed.

Instance andRV p1 p2 q1 q2 :
   RView q1 p1 -> RView q2 p2 ->
   RView (q1 /\ q2) (p1 && p2) | 90.
Proof.
move=> [v1] [v2]; split.
by apply: (iffP andP) => -[] /v1 ? /v2 ?; split.
Qed.

Instance orRV p1 p2 q1 q2 :
   RView q1 p1 -> RView q2 p2 ->
   RView (q1 \/ q2) (p1 || p2) | 90.
Proof.
move=> [v1] [v2]; split.
apply: (iffP orP) => -[ /v1 | /v2 ] ?; by [left|right].
Qed.

Lemma tedius2 b1 b2 b3 :
  b1 && b2 || b3 -> b3 || b1.
Proof.
move=> /rxP.
Admitted.

End Recursion.

(** #</div># *)

(** ------------------------------------- *)
(** #<div class="slide vfill"># 
** Rock solid?

 - no ;-)
 - Views are just terms, one can pass them
   arguments as in [/(v _ x)]

#</div># *)

(** ------------------------------------- *)
(** #<div class="slide"># *)
Module UsabilityIssues.
Import Recursion.

Check (rxP (true && false) _).
Check (rxP _ (true /\ false)).

Hint Mode RView + - : typeclass_instances.
Hint Mode RView - + : typeclass_instances.

Check (rxP _ _).

End UsabilityIssues.

(** #</div># *)
(** ------------------------------------- *)
(** #<div class="slide vfill"># 
** Cleaning up

 - View and RView
 - andV and andRV

#</div># *)
(** ------------------------------------- *)
(** #<div class="slide"># *)

Module OneView.

Definition vlevel := unit.

Definition vRec  : vlevel. Proof. by []. Qed.
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

Instance idV (b : bool) : View vStop b b | 99.
Proof. by split; apply: idP. Qed.

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

Hint Mode View + + - : typeclass_instances.
Hint Mode View + - + : typeclass_instances.

Lemma tedius2 b1 b2 b3 :
  b1 && b2 || b3 -> b3 || b1.
Proof.
move=> /xP. 
Admitted.

End OneView.

(** #</div># *)
(** ------------------------------------- *)
(** #<div class="slide"># *)
Module TheGameIsOn.

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
  View vl (exists2 x, x \in l & P x) (has p l). 
Proof.
  by (split; apply: (iffP hasP)) => [[x Hin /xPm ?]|[x Hin /xPm ?]]; exists x.
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
(* apply /lxP. *)
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


(** #</div># *)

(** ------------------------------------- *)
(** #<div class="slide vfill">#
** Wrapping up

 - Intergation is easy because view are terms
 - Type Classes enable user extensibility
 - Hardening is not obvious to me 

#</div># *)
(** -------------------------------------------- *)

(** #<div class='slide vfill'># 
** Spam

#<a href="http://math-comp.github.io/mcb">Mathematical Components (the book)</a>#

#<img src="http://math-comp.github.io/mcb/cover-front-web.png"/>#

#<a href="http://math-comp.github.io/mcb">http://math-comp.github.io/mcb</a>#

#</div>#
-------------------------------------------- *)

(**
#
<script>
alignWithTop = true;
current = 0;
slides = [];
function select_current() {
  for (var i = 0; i < slides.length; i++) {
    var s = document.getElementById('slideno' + i);
    if (i == current) {
      s.setAttribute('class','slideno selected');
    } else {
      s.setAttribute('class','slideno');
    }
  }	
}
function init_slides() {
  var toolbar = document.getElementById('panel-wrapper');
  if (toolbar) {
  var tools = document.createElement("div");
  var tprev = document.createElement("div");
  var tnext = document.createElement("div");
  tools.setAttribute('id','tools');
  tprev.setAttribute('id','prev');
  tprev.setAttribute('onclick','prev_slide();');
  tnext.setAttribute('id','next');
  tnext.setAttribute('onclick','next_slide();');
  toolbar.appendChild(tools);
  tools.appendChild(tprev);
  tools.appendChild(tnext);
  
  slides = document.getElementsByClassName('slide');
  for (var i = 0; i < slides.length; i++) {
    var s = document.createElement("div");
    s.setAttribute('id','slideno' + i);
    s.setAttribute('class','slideno');
    s.setAttribute('onclick','goto_slide('+ i +');');
    s.innerHTML = i;
    tools.appendChild(s);
  }
  select_current();
  } else {
  //retry later
  setTimeout(init_slides,100);	  
  }
}
function on_screen(rect) {
  return (
    rect.top >= 0 &&
    rect.top <= (window.innerHeight || document.documentElement.clientHeight)
  );
}
function update_scrolled(){
  for (var i = 0; i < slides.length; i++) {
    var rect = slides[i].getBoundingClientRect();
      if (on_screen(rect)) {
        current = i;
        select_current();	
    }
  }
}
function goto_slide(n) {
  current = n;
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function next_slide() {
  current++;
  if (current >= slides.length) { current = slides.length - 1; }
  var element = slides[current];
  console.log(element);
  element.scrollIntoView(alignWithTop);
  select_current();
}
function prev_slide() {
  current--;
  if (current < 0) { current = 0; }
  var element = slides[current];
  element.scrollIntoView(alignWithTop);
  select_current();
}
window.onload = init_slides;
window.onscroll = update_scrolled;
</script>
# *)
