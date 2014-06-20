Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint rat tuple.
Require Import interval matrix mxtens mxalgebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
(* Local Open Scope ring_scope. *)

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

Lemma extelt_ord_max  n (X : finType) (x : X) (s : {ffun 'I_n -> X}) :
  (extelt x s) ord_max = x.
Proof.
rewrite /extelt.
rewrite ffunE.
rewrite unlift_none.
done.
Qed.

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

Definition ctmat1 := (\matrix_(i < 3, j < 3)
  (nth [::] [:: [:: 1%:Z ; 1 ; 1 ]
              ; [:: -1   ; 1 ; 1 ]
              ; [::  0   ; 0 ; 1 ] ] i)`_j)%R.


Lemma mul2n n : (2 * n = n + n)%N. Proof. by rewrite mulSn mul1n. Qed.
Lemma mul3n n : (3 * n = n + (n + n))%N. Proof. by rewrite !mulSn addn0. Qed.

Definition lexi n (s : {set {ffun 'I_n -> 'I_3}}) : 'I_(#|s|) -> {ffun 'I_n -> 'I_3}.
Admitted.

Definition sign (i : 'I_3) : int :=
  if i == ord0 then 0%R else if i == ord_max then -1%R else 1%R.
Definition expo (i : 'I_3) : nat :=
  if i == ord0 then 0%N else if i == ord_max then 2%N else 1%N.

Definition mat n (s : {set Signs n}) (a : {set Expos n}) :
  'M[rat]_(#|s|, #|a|) := (\matrix_(i,j) (\prod_k (sign (@lexi _ s i k)) ^+ (expo (@lexi _ a j k)))%:Q)%R.

Definition adapted n (s : {set Signs n}) (a : {set Expos n}) :=
  (#|s| == #|a|) && row_free (mat s a).

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
    | 0     => fun S => S
    | n'.+1 => fun S => \bigcup_(i : 'I_3) extset i (adapt (Xi S i.+1))
  end S. 

Lemma adapt_monotonic n (S S' : {set Signs n}) :
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // extsetS IHn // Xi_monotonic.
Qed.

Definition restrict n (b : {ffun 'I_n.+1 -> 'I_3}) : {ffun 'I_n -> 'I_3} :=
  [ffun i => b (lift ord_max i)].

Lemma restrictK n (b : {ffun 'I_n.+1 -> 'I_3}) :
  extelt (b ord_max) (restrict b) = b.
Proof.
apply/ ffunP.
move=> i.
rewrite /extelt /restrict.
rewrite ffunE.
case: unliftP.
  move=> j.
  move=> i_def.
  rewrite ffunE.
  rewrite i_def.
  done.
move=> i_def.
rewrite i_def.
done.
Qed.

Lemma exteltK  n (b : {ffun 'I_n -> 'I_3}) (x : 'I_3) :
  restrict (extelt x b) = b.
Proof.
apply/ ffunP.
move=> i.
rewrite /restrict.
rewrite ffunE.
rewrite /extelt.
rewrite ffunE.
rewrite liftK.
done.
Qed.


Print pcancel.

Lemma in_adapt  n (S : {set Signs n.+1}) (a : Expos n.+1) :
  (a \in adapt S) = ((restrict a) \in adapt (Xi S (a ord_max).+1)).
Proof.
apply/idP/idP; last first.
  move=> ra_adaptXi.
  rewrite /=.
  About bigcupP.
  apply/ bigcupP.
  exists (a ord_max).
    done.
  About imsetP.
  apply/ imsetP.
  exists (restrict a).
    by apply: ra_adaptXi.
  by rewrite restrictK.
rewrite /=; move/ bigcupP.
case.
move=> i.
move=> _.
move/ imsetP.
case.
move=> a1.
move=> a1_adaptXi.
move=> def_a.
rewrite def_a.
rewrite exteltK.
rewrite extelt_ord_max.
by rewrite a1_adaptXi.
Qed.

Lemma fintype1 (T : finType) (x : T) : #|T| = 1 -> all_equal_to x.
Proof.
move=> /eqP T1 y; apply: contraTeq T1 => neq_yx.
suff: #|T| >= #|[set x ; y]|.
  by rewrite cards2 eq_sym neq_yx eq_sym => /ltn_eqF ->.
rewrite subset_leqif_card //; apply/subsetP => z.
by case/set2P => ->; rewrite predT_subset.
Qed.

Lemma adapt_down_closed  n (S : {set Signs n}) (a b : Expos n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype1 b) // card_ffun !card_ord.
move=> leq_ba.
rewrite !in_adapt.
move=> a_adaptXi.
have leq_rba : forall i : 'I_n, (restrict b) i <= (restrict a) i.
  move=> i.
  rewrite /restrict.
  rewrite !ffunE.
  by apply : leq_ba.
have := IHn _ _ (restrict b) leq_rba a_adaptXi.
apply : subsetP.
apply : adapt_monotonic.
apply : leq_Xi.
rewrite ltnS.
by apply : leq_ba.
Restart. (* Alternative direct proof. *)
elim: n => [|n IHn] in S a b *.
  by rewrite (fintype1 b) // card_ffun !card_ord.
move=> /= leq_ba /bigcupP /= [i _] /imsetP /= [a1 a1A a_def].
rewrite a_def in leq_ba * => {a_def a}.
apply/bigcupP; exists (b ord_max) => //.
apply/imsetP; exists (restrict b); last first.
  apply/ffunP => j. rewrite ffunE.
  by case: unliftP => [k|] -> //; rewrite ffunE.
apply: (IHn _ a1) => [j|].
  by rewrite ffunE (leq_trans (leq_ba _)) // ffunE liftK.
apply: subsetP (adapt_monotonic _) _ a1A.
by rewrite leq_Xi // ltnS (leq_trans (leq_ba _)) // ffunE unlift_none.
Qed.

Lemma card_adapt n (S : {set Signs n}) : #|adapt S| = #|S|.
Proof.
elim: n => [//|n IHn] in S *.
admit.
Qed.

Lemma adapt_adapted n (S : {set Signs n}) : adapted S (adapt S).
Proof.
elim: n S.
  move=> S.
  rewrite /adapted eqxx /= row_free_unit.
  have : #|S| <= 1.
    rewrite (@leq_trans #|[set: Signs 0]|) // ?subset_leqif_card ?subsetT //.
    by rewrite cardsT card_ffun !card_ord.
  rewrite leq_eqVlt ltnS leqn0 orbC cards_eq0; move/predU1P => [->|/eqP S1].
    by move: (mat _ _); rewrite cards0 => M; rewrite unitmxE det_mx00.
  suff ->: mat S S = 1%:M%R by rewrite unitmx1.
  apply/matrixP => i j; rewrite !mxE big_ord0.
  by rewrite S1 in i j *; rewrite !ord1 eqxx.
move=> n IHn S; rewrite /adapted {1}card_adapt eqxx // andTb.
(* rewrite -kermx_eq0; apply/eqP. *)
(* have : mat S (adapt S)  col_mx (mat (Xi S 1) () *)
suff: forall (L : 'rV__), L *m mat S (adapt S) = 0%R ->  L = 0%R.
  move=> Hmat; rewrite -kermx_eq0; apply/eqP. 
  apply/row_matrixP => i; rewrite row0; apply/Hmat.
  by apply/sub_kermxP; rewrite row_sub.
move=> L.
move/matrixP.



apply/row_freeP => /=.
  rewrite /mat.

  move/set0Pn => [x].

  have : #|S| <= 1.
    rewrite (@leq_trans #|[set: Signs 0]|) // ?subset_leqif_card ?subsetT //.
    by rewrite cardsT card_ffun !card_ord.
  
     
    have /subset_leqif_cards := subsetT S.
    rewrite cardsT card_ffun.
    rewrite !card_ord expn0.
    apply/eqP.
    rewrite -leqn0.
    
    rewrite card_ffun.
  move: (mat _ _).
  rewrite cards0.
  rewrite unitmxE.
  rewrite det_mx00.
  About cards0.
  have: S = set0.
    admit.
  case: _ /.
  rewrite eqxx.
  rewrite conform_mx_id.

  rewrite cards0.
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