Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint tuple.
Require Import interval matrix mxtens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section SignDet.

(* Set Printing All. *)

(* Fixpoint signdet (n : nat) (taq : ('I_n -> 'I_3) -> int) {struct n} : *)
(*   {m : nat & (m.-tuple 'I_3 * m.-tuple 'I_3 * 'M[int]_m)%type} := *)
(*   match n with *)
(*     | 0     => (existT _ 0 ([tuple], [tuple], 0%R)) *)
(*     | n'.+1 =>  *)
(*       let taq' (f : 'I_n' -> 'I_3) :=  *)
(*             taq (fun (i : 'I_n) =>  *)
(*                    if (i < n') =P true is ReflectT P *)
(*                    then f (Ordinal P) else ord0) in *)
(*       let: existT m (sc, ada, M) := signdet taq' in *)
               
(*                (existT _ 0 ([tuple], [tuple], 0%R)) *)
(*   end. *)

Definition Signs n := {ffun 'I_n -> 'I_3}.
Definition Expos n := {ffun 'I_n -> 'I_3}.

Definition extelt n (X : finType) (x : X) (s : {ffun 'I_n -> X}) : {ffun 'I_n.+1 -> X} :=
  [ffun i => if unlift ord_max i is Some j then s j else x].

Lemma eq_extelt n (X : finType) (x x' : X) (s s' : {ffun 'I_n -> X}) :
  (extelt x s == extelt x' s') = (x == x') && (s == s').
Proof.
apply/eqP/idP; last by move=> /andP [/eqP -> /eqP ->].
move => /ffunP eqss'.
have := eqss' ord_max.
  rewrite !ffunE /= unlift_none => ->; rewrite eqxx /=.
apply/eqP/ffunP => i.
have := eqss' (lift ord_max i).
by rewrite !ffunE liftK.
Qed.



(* Definition extset n (X : finType) (x : X) (S : {set {ffun 'I_n -> X}}) : *)
(*    {set {ffun 'I_n.+1 -> X}} := *)
(*    [set s : {ffun 'I_n.+1 -> X} | (s ord_max == x) *)
(*    && ([ffun x : 'I_n => s (lift ord_max x)] \in S)]. *)

Definition extset n (X : finType) (x : X) (S : {set {ffun 'I_n -> X}}) :
   {set {ffun 'I_n.+1 -> X}} :=  [set extelt x s | s in S].

Lemma extsetS n (X : finType) (x : X) (S S' : {set {ffun 'I_n -> X}}) :
  (extset x S \subset extset x S') = (S \subset S').
Proof.
apply/idP/idP.
  move/subsetP => SS'.
  apply/subsetP => /=.
  move=> s sS.
  have extsS: extelt x s \in extset x S by rewrite mem_imset.
  have := SS' _ (* (extelt x s) *) extsS.
  move/imsetP => [/= s' s'S'].
  by move/eqP; rewrite eq_extelt => /andP [_ /eqP ->].
move=> /subsetP SS'.
apply/subsetP=> /= s.
move=> /imsetP [/= s1 s1S ->].
by rewrite mem_imset // SS'.
Qed.

Definition tvec (n : nat) (taq : ('I_n -> 'I_3) -> int) (a : {set Expos n}) :
   'rV[int]_(#|a|).
Admitted.

Definition cnonnull (n m : nat) (s : {set Signs n}) (c : 'rV[int]_(3 * m)) :
   {set Expos n}. (* morally m = #|s| *)
Admitted.

Definition ctmat1 := \matrix_(i < 3, j < 3)
  (nth [::] [:: [:: 1%:Z ; 1 ; 1 ]
              ; [:: -1   ; 1 ; 1 ]
              ; [::  0   ; 0 ; 1 ] ] i)`_j.


Lemma mul2n n : (2 * n = n + n)%N. Proof. by rewrite mulSn mul1n. Qed.
Lemma mul3n n : (3 * n = n + (n + n))%N. Proof. by rewrite !mulSn addn0. Qed.

Definition lexi n (s : {set {ffun 'I_n -> 'I_3}}) : 'I_(#|s|) -> {ffun 'I_n -> 'I_3}.
Admitted.

Definition sign (i : 'I_3) : int :=
  if i == ord0 then -1 else if i == ord_max then 1 else 0.
Definition expo (i : 'I_3) : nat :=
  if i == ord0 then 0%N else if i == ord_max then 2%N else 1%N.

Definition mat n (s : {set Signs n}) (a : {set Expos n}) :
  'M[int]_(#|s|, #|a|) := \matrix_(i,j) \prod_k (sign (@lexi _ s i k)) ^+ (expo (@lexi _ a j k)).

Definition adapted n (s : {set Signs n}) (a : {set Expos n}) :=
  (#|s| == #|a|) && (conform_mx (0 :'M[int]_(#|s|)) (mat s a) \in unitmx).

(* Definition subst  X (P : X -> Type) (x y : X) (e : x = y) : P x -> P y := *)
(*   let: erefl := e in id. *)

Definition Xi n (S : {set Signs n.+1}) m :=
  [set s : {ffun 'I_n -> 'I_3} 
  | [exists xs : m.-tuple 'I_3, 
     uniq xs && [forall x in xs, extelt x s \in S]]].

Lemma Xi_monotonic n (S S' : {set Signs n.+1}) m :
  S \subset S' -> Xi S m \subset Xi S' m.
Proof.
move=> /subsetP subSS'; apply/subsetP => /= s; rewrite !in_set.
move=> /existsP /= [xs /andP[uxs /'forall_implyP /= HS]].
apply/existsP; exists xs; rewrite uxs //=.
by apply/'forall_implyP => /= x xxs; rewrite subSS' ?HS.
Qed.

Lemma leq_Xi n (S : {set Signs n.+1}) m p : 
  (p <= m)%N -> (Xi S m) \subset (Xi S p).
Proof.
move=> lpm; apply/subsetP => /= s.
rewrite !in_set => /existsP [/= xs /andP [uxs /'forall_implyP /= inS]].
have size_tpxs : size (take p xs) == p.
  rewrite size_take size_tuple.
  by rewrite ltn_neqAle lpm andbT; have [->|//] := altP (p =P m).
apply/existsP => /=; exists (Tuple size_tpxs) => /=.
rewrite (subseq_uniq _ uxs) /=; last first.
  by rewrite -{2}(cat_take_drop p xs) prefix_subseq.
apply/'forall_implyP => /= x /= xxs; apply: inS.
exact: mem_take xxs.
Qed.

Fixpoint adapt n (S : {set Signs n}) : {set Expos n} :=
  match n return {set Signs n} -> {set Expos n} with
    | 0 => fun _ => set0
    | n'.+1 => fun S =>
      let A m := adapt (Xi S m) in
      (extset (0%R : 'F_3) (A 1%N)) :|:
      (extset (1%R : 'F_3) (A 2%N)) :|:
      (extset (2%:R : 'F_3) (A 3%N))
  end S. 

Lemma adapt_monotonic : forall n (S S' : {set Signs n}),
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim; first by move=> S S' subSS' /=; rewrite sub0set.
move=> n IHn S S' subSS' /=.
by do !apply: setUSS; rewrite extsetS IHn // Xi_monotonic.
Qed.


Lemma adapt_downward_closed n (S : {set Signs n}) (a b : Expos n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *; first by rewrite in_set0.
  move=> leq_ba.
  set a' := [ffun i => if i == ord_max then b i else a i].

  have := leq_ba ord_max.
  case: (a ord_max) => [[|[|[|//]]]] leqa3 /=.
    rewrite leqn0.


  (* move=> leq_ba; rewrite !in_set /= -orbA. *)
  (* case/or3P. *)
Admitted.
  

Lemma adapt_adapted n (S : {set Signs n}) : adapted S (adapt S).
Proof.
admit.
Qed.

(* Fixpoint adapt n (S : {set Signs n}) : {set Expos n} := *)
(*   match n return {set Signs n} -> {set Expos n} with *)
(*     | 0 => fun _ => set0 *)
(*     | n'.+1 => fun S => *)
(*       let S1 := [ set s : {ffun 'I_n' -> 'I_3}  *)
(*                 | [exists s' in S, [ffun x : 'I_n' => s' (lift ord_max x)] == s]] in *)
(*       let S2 := [ set s : {ffun 'I_n' -> 'I_3}  *)
(*                 | [exists s' in S, [exists s'' in S, *)
(*                   [&& s' != s'', [ffun x : 'I_n' => s' (lift ord_max x)] == s *)
(*                                & [ffun x : 'I_n' => s'' (lift ord_max x)] == s]]]] in *)
(*       let S3 := [ set s : {ffun 'I_n' -> 'I_3}  *)
(*                 | [exists s' in S, [exists s'' in S, [exists s''' in S, *)
(*                   [&& [&& s' != s'', s' != s''' & s'' != s'''], *)
(*                   [ffun x : 'I_n' => s' (lift ord_max x)] == s, *)
(*                   [ffun x : 'I_n' => s'' (lift ord_max x)] == s & *)
(*                   [ffun x : 'I_n' => s''' (lift ord_max x)] == s]]]]] in *)
(*       let A1 := adapt S1 in *)
(*       let A2 := adapt S2 in *)
(*       let A3 := adapt S3 in *)
(*       (extset (0%R : 'F_3) A1) :|: (extset (1%R : 'F_3) A2) :|: (extset (2%:R : 'F_3) A3) *)
(*   end S.  *)



(* Lemma adapt_monotonic: forall n (S S' : {set Signs n}), *)
(*   S \subset S' -> adapt S \subset adapt S'. *)
(* Proof. *)
(* elim; first by move=> S S' subSS' /=; rewrite sub0set. *)
(* move=> n IHn S S' /subsetP subSS' /=. *)
(* apply: setUSS. *)
(*   apply: setUSS. *)
(*     rewrite extsetS IHn //. *)
(*     apply/subsetP => /= s. *)
(*     rewrite !in_set => /existsP /= [s1 /andP [s1S /eqP <-]]. *)
(*     by apply/existsP; exists s1; rewrite subSS' /=. *)
(*   rewrite extsetS IHn //. *)
(*   apply/subsetP => /= s. *)
(*   rewrite !in_set => /existsP /= [s1 /andP [s1S /existsP /= *)
(*     [s2 /and3P [s2S neq_s1s2 /andP [s1_def s2_def]]]]]. *)
(*   apply/existsP; exists s1; rewrite subSS' //=. *)
(*   apply/existsP; exists s2; rewrite subSS' //=. *)
(*   by rewrite neq_s1s2 s1_def s2_def. *)
(* rewrite extsetS IHn //. *)
(* apply/subsetP => /= s. *)
(* rewrite !in_set => /existsP /= [s1 /andP [s1S /existsP /= *)
(*   [s2 /andP [s2S /existsP /= [s3 /and3P [s3S /and3P [ns12 ns13 ns23] *)
(*   /and3P [s1_def s2_def s3_def]]]]]]]. *)
(* apply/existsP; exists s1; rewrite subSS' //=. *)
(* apply/existsP; exists s2; rewrite subSS' //=. *)
(* apply/existsP; exists s3; rewrite subSS' //=. *)
(* by rewrite ns12 ns13 ns23 s1_def s2_def s3_def. *)
(* Qed. *)



Definition nonEmptySigns n (taq : ('I_n -> 'I_3) -> int) : {set Signs n}.
Admitted.

Definition signdet (n : nat) (taq : ('I_n -> 'I_3) -> int)  :
  {sa : {set Signs n} * {set Expos n}
        & 'M[int]_(#|sa.1|, #|sa.2|)}.
Proof.
elim: n taq.
  move=> taq; exists (set0, set0); exact 0.
move=> n' IHn taq.
set taq' := fun f => taq (fun (i : 'I_n'.+1) => 
                 if (i < n')%N =P true is ReflectT P
                   then f (Ordinal P) else ord0).
have [[s a] /= M] := IHn taq'.
(* set s' := cnonnull s (row_mx (tvec taq (extset ord0 a)) *)
(*                  (row_mx (tvec taq (extset (1%R : 'F_3) a)) (tvec taq (extset (2%:R : 'F_3) a))) *m  *)
(*                castmx (mul3n _, erefl) (invmx (M *t ctmat1))). *)

(*  := *)
(*   match n with *)
(*     | 0     => (existT (fun sa : {set Signs n} * {set Expos n} *)
(*                          => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R) *)
(*     | n'.+1 =>  *)
(*       let taq' (f : 'I_n' -> 'I_3) :=  *)
(*           taq (fun (i : 'I_n) =>  *)
(*                  if (i < n')%N =P true is ReflectT P *)
(*                    then f (Ordinal P) else ord0) in *)
(*       let: existT (s, a) M := signdet taq' in *)
(*       let c := cnonnull s (row_mx (tvec taq (extset ord0 a)) *)
(*                  (row_mx (tvec taq (extset 1%R a)) (tvec taq (extset 2%R a))) *m  *)
(*                castmx (mul3n _, erefl) (invmx (M *t ctmat1))) in *)



(*       (* let s' :=  (extset 0%R s) :|: (extset 1%R s) :|: (extset 2%R s) in *) *)
(*       (* let a' :=  (extset 0%R a) :|: (extset 1%R a) :|: (extset 2%R a) in *) *)


(*  (existT (fun sa : {set Signs n} * {set Expos n} *)
(*                          => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R) *)
(*   end. *)

Admitted.

Definition signdetS (n : nat) (taq : ('I_n -> 'I_3) -> int) :=
  let: existT sa _ := signdet taq in sa.1.

Definition signdetAda (n : nat) (taq : ('I_n -> 'I_3) -> int) :=
  let: existT sa _ := signdet taq in sa.2.

Definition signdetM_subdef (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  'M[int]_(#|signdetS taq|,#|signdetAda taq|).
Admitted.

Lemma signdet_sizeP (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  #|signdetS taq| = #|signdetAda taq|.
Proof.
Admitted.

Definition signdetM  (n : nat) (taq : ('I_n -> 'I_3) -> int) :
  'M[int]_(#|signdetS taq|,#|signdetS taq|) :=
  castmx (erefl, esym (signdet_sizeP taq)) (signdetM_subdef taq).

Lemma unit_signdet  (n : nat) (taq : ('I_n -> 'I_3) -> int) : 
  signdetM taq \in unitmx.
Proof.
Admitted.


  (* {m : nat & m.-tuple 'I_3 * m.-tuple 'I_3 * 'M[int]_m)%type} := *)
  (* match n with *)
  (*   | 0     => (existT _ 0 ([tuple], [tuple], 0%R)) *)
  (*   | n'.+1 =>  *)
  (*     let taq' (f : 'I_n' -> 'I_3) :=  *)
  (*           taq (fun (i : 'I_n) =>  *)
  (*                  if (i < n') =P true is ReflectT P *)
  (*                  then f (Ordinal P) else ord0) in *)
  (*     let: existT m (sc, ada, M) := signdet taq' in *)
               
  (*              (existT _ 0 ([tuple], [tuple], 0%R)) *)
  (* end. *)


End SignDet.