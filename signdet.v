Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint rat tuple.
Require Import interval matrix mxtens mxalgebra binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Num.Def Pdiv.Ring Pdiv.ComRing.

Local Open Scope ring_scope.
Local Open Scope nat_scope.
(* Local Open Scope ring_scope. *)

Section extrassr.

Lemma fintype1 (T : finType) (x : T) : #|T| = 1 -> all_equal_to x.
Proof.
move=> /eqP T1 y; apply: contraTeq T1 => neq_yx.
suff: #|T| >= #|[set x ; y]|.
  by rewrite cards2 eq_sym neq_yx eq_sym => /ltn_eqF ->.
rewrite subset_leqif_card //; apply/subsetP => z.
by case/set2P => ->; rewrite predT_subset.
Qed.

Lemma bump_small n i : i < n -> bump n i = i.
Proof. by move=> ltin; rewrite /bump leqNgt ltin add0n. Qed.

Lemma lift_ord_max n (i : 'I_n) :
   lift ord_max i = widen_ord (leqnSn n) i.
Proof. by apply: val_inj=> /=; rewrite bump_small. Qed.

Lemma cards_draws (T : finType) (B : {set T}) k :
  #|[set A : {set T} | A \subset B & #|A| == k]| = 'C(#|B|, k).
Proof.
have [ltTk | lekT] := ltnP #|B| k.
  rewrite bin_small // eq_card0 // => A.
  rewrite inE eqn_leq [k <= _]leqNgt.
  have [AsubB /=|//] := boolP (A \subset B).
  by rewrite (leq_ltn_trans (subset_leq_card AsubB)) ?andbF.
apply/eqP; rewrite -(eqn_pmul2r (fact_gt0 k)) bin_ffact // eq_sym.
rewrite -sum_nat_dep_const -{1 3}(card_ord k).
rewrite -card_inj_ffuns_on -sum1dep_card.
pose imIk (f : {ffun 'I_k -> T}) := f @: 'I_k.
rewrite (partition_big imIk (fun A => (A \subset B) && (#|A| == k))) /=
  => [|f]; last first.
  move=> /andP [/ffun_onP f_ffun /injectiveP inj_f].
  rewrite card_imset ?card_ord // eqxx andbT.
  by apply/subsetP => x /imsetP [i _ ->]; rewrite f_ffun.
apply/eqP; apply: eq_bigr => A /andP [AsubB /eqP cardAk].
have [f0 inj_f0 im_f0]: exists2 f, injective f & f @: 'I_k = A.
  rewrite -cardAk; exists enum_val; first exact: enum_val_inj.
  apply/setP=> a; apply/imsetP/idP=> [[i _ ->] | Aa]; first exact: enum_valP.
  by exists (enum_rank_in Aa a); rewrite ?enum_rankK_in.
rewrite (reindex (fun p : {ffun _} => [ffun i => f0 (p i)])) /=; last first.
  pose ff0' f i := odflt i [pick j | f i == f0 j].
  exists (fun f => [ffun i => ff0' f i]) => [p _ | f].
    apply/ffunP=> i; rewrite ffunE /ff0'; case: pickP => [j | /(_ (p i))].
      by rewrite ffunE (inj_eq inj_f0) => /eqP.
    by rewrite ffunE eqxx.
  rewrite -im_f0 => /andP[/andP[/ffun_onP f_ffun /injectiveP injf] /eqP im_f].
  apply/ffunP=> i; rewrite !ffunE /ff0'; case: pickP => [y /eqP //|].
  have /imsetP[j _ eq_f0j_fi]: f i \in f0 @: 'I_k by rewrite -im_f mem_imset.
  by move/(_ j)=> /eqP[].
rewrite -ffactnn -card_inj_ffuns -sum1dep_card; apply: eq_bigl => p.
rewrite -andbA.
apply/and3P/injectiveP=> [[_ /injectiveP inj_f0p _] i j eq_pij | inj_p].
  by apply: inj_f0p; rewrite !ffunE eq_pij.
set f := finfun _.
have injf: injective f by move=> i j; rewrite !ffunE => /inj_f0; exact: inj_p.
have imIkf : imIk f == A.
  rewrite eqEcard card_imset // cardAk card_ord leqnn andbT -im_f0.
  by apply/subsetP=> x /imsetP[i _ ->]; rewrite ffunE mem_imset.
split; [|exact/injectiveP|exact: imIkf].
apply/ffun_onP => x; apply: (subsetP AsubB).
by rewrite -(eqP imIkf) mem_imset.
Qed.

End extrassr.

Section SignDet.

Definition extelt n (X : finType) (x : X) (s : X ^ n) : X ^ n.+1 :=
  [ffun i => if unlift ord_max i is Some j then s j else x].

Definition restrict n (X : finType) (b : X ^ n.+1) : X ^ n :=
  [ffun i => b (lift ord_max i)].

Lemma restrictK n (X : finType) (b : X ^ n.+1) :
  extelt (b ord_max) (restrict b) = b.
Proof.
by apply/ffunP=> i; rewrite ffunE; case: unliftP => [j|] ->; rewrite ?ffunE.
Qed.

Lemma exteltK n (X : finType) (x : X) (b : X ^ n) : restrict (extelt x b) = b.
Proof. by apply/ffunP=> i; rewrite !ffunE liftK. Qed.

Lemma extelt_ord_max  n (X : finType) (x : X) (s : X ^ n) :
  (extelt x s) ord_max = x.
Proof. by rewrite /extelt ffunE unlift_none. Qed.

Lemma eq_extelt n (X : finType) (x x' : X) (s s' : X ^ n) :
  (extelt x s == extelt x' s') = (x == x') && (s == s').
Proof.
apply/eqP/idP; last by move=> /andP [/eqP -> /eqP ->].
move=> /ffunP eqss'; have := eqss' ord_max.
rewrite !ffunE /= unlift_none => ->; rewrite eqxx /=.
apply/eqP/ffunP => i; have := eqss' (lift ord_max i).
by rewrite !ffunE liftK.
Qed.

Definition extset n (X : finType) (x : X) (S : {set X ^ n}) :
   {set X ^ n.+1} :=  [set extelt x s | s in S].

Lemma mem_extset n (X : finType) (x x' : X) s (S : {set X ^ n}) :
  extelt x s \in extset x' S = (x == x') && (s \in S).
Proof.
apply/imsetP/idP => /= [[s' s'S /eqP]|/andP [/eqP<-]]; last by exists s.
by rewrite eq_extelt => /andP [-> /eqP ->].
Qed.

Lemma mem_extset_r n (X : finType) (x : X) s (S : {set X ^ n}) :
  extelt x s \in extset x S = (s \in S).
Proof. by rewrite mem_extset eqxx. Qed.

Lemma extset0 n (X : finType) (x : X) : extset x set0 = set0 :> {set X ^ n.+1}.
Proof. by rewrite /extset imset0. Qed.

Lemma extset_eq0 n (X : finType) (x : X) (S : {set X ^ n}) :
  (extset x S == set0) = (S == set0).
Proof.
apply/eqP/eqP => [ext_eq0|->]; last by rewrite extset0.
by apply/setP => s; rewrite -(mem_extset_r x) ext_eq0 !in_set0.
Qed.

Lemma eq_extset n (X : finType) (x y : X) (S S' : {set X ^ n}) :
  (extset x S == extset y S') = ((S != set0) ==> (x == y)) && (S == S').
Proof.
apply/eqP/idP => [|/andP [/implyP eq_xy /eqP<- //]]; last first.
  case: (altP eqP) eq_xy => [-> _|_ /(_ isT) /eqP -> //].
  by rewrite /extset !imset0.
have [-> /eqP|/set0Pn [s mem_s] eq_exts] /= := altP (S =P set0).
  by rewrite eq_sym extset0 extset_eq0 => /eqP ->.
move: mem_s; rewrite -(mem_extset_r x) eq_exts mem_extset => /andP [eq_xy _].
rewrite -(eqP eq_xy) {eq_xy y s} eqxx /= in eq_exts *.
by apply/eqP/setP => s; rewrite -(mem_extset_r x) eq_exts mem_extset_r.
Qed.

Lemma subset_ext n (X : finType) (x : X) (S S' : {set X ^ n}) :
  (extset x S \subset extset x S') = (S \subset S').
Proof.
apply/subsetP/subsetP => SS' s.
  by move/(mem_imset (extelt x))/SS'; rewrite mem_extset_r.
by case/imsetP=> s' s'S ->; rewrite mem_extset_r SS'.
Qed.

(* Definition tvec (n : nat) (taq : ('I_n -> 'I_3) -> int) (a : {set Expos n}) : *)
(*    'rV[int]_(#|a|). *)
(* Admitted. *)

(* Definition cnonnull (n m : nat) (s : {set Signs n}) (c : 'rV[int]_(3 * m)) : *)
(*    {set Expos n}. (* morally m = #|s| *) *)
(* Admitted. *)

Definition ctmat1 := (\matrix_(i < 3, j < 3)
  (nth [::] [:: [:: 1%:Z ; 1 ; 1 ]
              ; [:: -1   ; 1 ; 1 ]
              ; [::  0   ; 0 ; 1 ] ] i)`_j)%R.


Lemma mul2n n : (2 * n = n + n)%N. Proof. by rewrite mulSn mul1n. Qed.
Lemma mul3n n : (3 * n = n + (n + n))%N. Proof. by rewrite !mulSn addn0. Qed.

(* Definition lexi n (S : {set 'I_3 ^ n}) : 'I_(#|S|) -> 'I_3 ^ n := *)
(*   enum_val. *)

(* Lemma lexiP n (S : {set 'I_3 ^ n}) (i :'I_(#|S|)) : lexi i \in S. *)
(* Proof. exact: enum_valP. Qed. *)


(* Lemma unlexiK n (s : {set exp 'I_3 n}) : *)
(*    {in [set lexi x | x in 'I_(#|s|)], cancel (unlexi s) (@lexi _ s)}. *)
(* Admitted. *)

(* Lemma unlexiK n (s : {set exp 'I_3 n}) j : *)
(*   (lexi (unlexi s j) == j) = (j \in s). *)
(* Proof. *)
(* apply/eqP/idP => [<-|]. *)

(* Definition subst  X (P : X -> Type) (x y : X) (e : x = y) : P x -> P y := *)
(*   let: erefl := e in id. *)

Definition Xi n (X : finType) (S : {set X ^ n.+1}) (m : nat) :=
  [set s : X ^ n | [exists E : {set X}, (#|E| == m)
                   && [forall x in E, extelt x s \in S]]].

Lemma Xi_monotonic n (X : finType) (S S' : {set X ^ n.+1}) m :
  S \subset S' -> Xi S m \subset Xi S' m.
Proof.
move=> /subsetP subSS'; apply/subsetP => /= s; rewrite !in_set.
move=> /existsP /= [xs /andP[uxs /'forall_implyP /= HS]].
apply/existsP; exists xs; rewrite uxs //=.
by apply/'forall_implyP => /= x xxs; rewrite subSS' ?HS.
Qed.

Lemma leq_Xi n (X : finType) (S : {set X ^ n.+1}) m p :
  (p <= m)%N -> (Xi S m) \subset (Xi S p).
Proof.
move=> lpm; apply/subsetP => /= s.
rewrite !in_set => /existsP [/= E /andP [/eqP cardE /'forall_implyP /= inS]].
have /set0Pn [A] : [set A : {set X} | A \subset E & #|A| == p] != set0.
  by rewrite -card_gt0 cards_draws bin_gt0 cardE.
rewrite inE => /andP [AsubE cardA]; apply/existsP; exists A; rewrite cardA.
by apply/forallP => x; apply/implyP => /(subsetP AsubE); apply: inS.
Qed.

Notation Signs n := ('I_3 ^ n)%type.
Notation Expos n := ('I_3 ^ n)%type.

Definition sign (i : 'I_3) : int :=
  if i == ord0 then 0%R else if i == ord_max then -1%R else 1%R.
Definition expo (i : 'I_3) : nat :=
  if i == ord0 then 0%N else if i == ord_max then 2%N else 1%N.

Definition mat_coef n (i : Signs n) (j : Expos n) :=
  (\prod_k (sign (i k)) ^+ (expo (j k)))%:Q%R.

Definition mat n (s : {set Signs n}) (a : {set Expos n}) : 
  'M[rat]_(#|s|, #|a|) :=
    \matrix_(i,j) mat_coef (enum_val i) (enum_val j).

Definition adapted n (s : {set Signs n}) (a : {set Expos n}) :=
  (#|s| == #|a|) && row_free (mat s a).

Fixpoint adapt n (S : {set Signs n}) : {set Expos n} :=
  match n return {set Signs n} -> {set Expos n} with
    | 0     => fun S => S
    | n'.+1 => fun S => \bigcup_(i : 'I_3) extset i (adapt (Xi S i.+1))
  end S.

Lemma adapt_monotonic n (S S' : {set Signs n}) :
  S \subset S' -> adapt S \subset adapt S'.
Proof.
elim: n => [//|n IHn] in S S' * => subSS' /=; apply/bigcupsP => i _.
by rewrite (bigcup_max i) // subset_ext IHn // Xi_monotonic.
Qed.

Lemma in_adapt  n (S : {set Signs n.+1}) (a : Expos n.+1) :
  (a \in adapt S) = (restrict a \in adapt (Xi S (a ord_max).+1)).
Proof.
move=> /=; apply/bigcupP/idP => [[i _ /imsetP [s sAXi ->]]|].
  by rewrite exteltK extelt_ord_max.
by move=> raAXi; exists (a ord_max); rewrite // -{1}[a]restrictK mem_extset_r.
Qed.

Lemma adapt_down_closed  n (S : {set Signs n}) (a b : Expos n) :
  (forall i, b i <= a i)%N -> a \in adapt S -> b \in adapt S.
Proof.
elim: n => [|/= n IHn] in S a b *.
  by move=> _; rewrite (fintype1 b) // card_ffun !card_ord.
move=> leq_ba; rewrite !in_adapt => raAXi.
have: restrict b \in adapt (Xi S (a ord_max).+1).
  by apply: IHn raAXi => i; rewrite !ffunE leq_ba.
by apply: subsetP; rewrite adapt_monotonic ?leq_Xi ?ltnS ?leq_ba.

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
elim: n => [//|n IHn] /= in S *; rewrite -cover_imset.
set P := (X in cover X); have /eqP <- : trivIset P.
  apply/trivIsetP => /= A B /imsetP [i _ ->] /imsetP [j _ ->].
  have [->|neq_ij _] := eqVneq i j; first by rewrite eqxx.
  rewrite -setI_eq0; apply: contraNT neq_ij => /set0Pn /= [e].
  rewrite inE => /andP [/imsetP [ei _ ->] /imsetP [ej _]] /eqP.
  by rewrite eq_extelt => /andP [].
rewrite big_imset /=; last first.
  move=> i j _ _ /= /eqP.
  rewrite eq_extset.
Admitted.  


(* transitivity #|cover [set extset i (adapt (Xi S i.+1)) | i : 'I_3]|. *)
(*   apply: eq_card => /= E; apply/bigcupP/bigcupP => /= [[i _ memE]|[A]]. *)
(*     by exists (extset i (adapt (Xi S i.+1))); first by apply: mem_imset. *)
(*   by move=> /imsetP [i _ ->] memE; exists i. *)
(* rewrite leq_card_cover. *)

(* rewrite -card_partition. *)
(* admit. *)
(* Qed. *)

Lemma prop1084 n (S : {set Signs n}) a :
 a \in adapt S -> 2 ^ #|[set i : 'I_n | a(i) != 0%R]| <= #|S|.
Proof.
move=> a_adapt.
pose B := [set b : Expos n | [forall i, (b i != ord0) ==> (b i == a i)]].
apply: (@leq_trans #|B|) => [{a_adapt}|]; last first.
  rewrite -(card_adapt S) subset_leq_card //; apply/subsetP => b.
  rewrite in_set => /forallP bP; apply: adapt_down_closed a_adapt => i.
  by have := bP i; rewrite implyNb => /orP [/eqP ->|/eqP ->].
suff -> : B = [set [ffun i => if i \in (I : {set _}) then a i else 0%R]
              | I in powerset [set i | a i != 0%R]].
  rewrite card_in_imset; first by rewrite card_powerset leqnn.
  move=> I J /=; rewrite !in_set => PI PJ eqIJ; apply/setP => i.
  have := congr1 (fun f : {ffun _ -> _} => f i == 0%R) eqIJ; rewrite !ffunE.
  have [] := (subsetP PI i, subsetP PJ i); rewrite in_set.
  case: (i \in I) => [/(_ isT) /negPf ->|_];
  by case: (i \in J) => // /(_ isT) /negPf ->.
apply/setP => b; rewrite in_set.
apply/'forall_implyP/imsetP => [bP|[I]]; last first.
  by rewrite powersetE => /subsetP IP -> i; rewrite !ffunE; case: ifP.
exists [set i | b i != 0%R].
  rewrite powersetE; apply/subsetP => i; rewrite !in_set => b_neq0.
  by rewrite -(eqP (bP _ _)).
apply/ffunP => i; rewrite ffunE in_set.
by case: ifPn => [/bP /eqP <- //|]; rewrite negbK => /eqP.
Qed.

Definition extension n (S : Signs n.+1) (s : Signs n) : Signs n.+1.
Admitted.

(* Lemma S_decomp n (S : {set Signs n.+1}) : *)
(*   S = [set extend  s | s in Xi S 1] *)


Lemma enum_rank_in_id (T : finType) (x0 : T)
  (A : pred T) (Ax0 : x0 \in A) (x : T) :
  (enum_val (enum_rank_in Ax0 x) == x) = (x \in A).
Proof.
by apply/eqP/idP => [<-|xA]; rewrite ?enum_valP ?enum_rankK_in ?eqxx.
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
  apply/matrixP => i j; rewrite /mat !mxE /mat_coef big_ord0.
  by rewrite S1 in i j *; rewrite !ord1 eqxx.
move=> n IHn S; rewrite /adapted {1}card_adapt eqxx // andTb.
(* rewrite -kermx_eq0; apply/eqP. *)
(* have : mat S (adapt S)  col_mx (mat (Xi S 1) () *)
suff: forall (L : 'rV__), L *m mat S (adapt S) = 0%R ->  L = 0%R.
  move=> Hmat; rewrite -kermx_eq0; apply/eqP.
  apply/row_matrixP => i; rewrite row0; apply/Hmat.
  by apply/sub_kermxP; rewrite row_sub.
move=> L LP.
have: (\sum_(i < #|S|) (L ord0 i)%:M *m
  \row_(j < #|adapt S|) mat_coef (enum_val i) (enum_val j) = 0)%R.
  apply/rowP => i; have /rowP /(_ i) := LP; rewrite !mxE => <-.
  elim/big_ind2: _ => [|x a y b|j _]; rewrite ?mxE //=.
    by move=> -> ->.
  by rewrite big_ord1 !mxE mulr1n.
(* pose F (i : Signs _) := ((L ord0 i)%:M *m \row_j mat_coef i (enum_val j))%R. *)
(* have /= := (@reindex _ _ _ _ _ (@enum_val n.+1 S) xpredT ). *)
have [S0|[s0 s0S]] := set_0Vmem S.
  rewrite S0 {S0} in L {LP} *; rewrite big1.
     by rewrite cards0 in L *; rewrite thinmx0.
  by case => m Hm; suff: false by []; rewrite cards0 in Hm.
rewrite (reindex_onto (enum_rank_in s0S) enum_val) //=; last first.
  by move=> i; rewrite enum_valK_in.
rewrite (eq_bigl _ _ (enum_rank_in_id _)).
rewrite (eq_bigr (fun i =>
  (L ord0 (enum_rank_in s0S i))%:M *m \row_j mat_coef i (enum_val j)%R)); last first.
  by move=> i iS; rewrite enum_rankK_in. 
Admitted.

Lemma extelt_small (X : finType) (x : X) n (i : 'I_n.+1)
  (b : X ^ n) (lt_in : i < n) :
  (extelt x b) i = b (Ordinal lt_in).
Proof.
rewrite ffunE; case: unliftP=> [j|] i_def; last first.
  by suff: false by []; rewrite i_def ltnn in lt_in *.
by congr (b _); apply: val_inj; rewrite /= i_def /= bump_small.
Qed.

Definition nonEmptySigns n (taq : ('I_n -> 'I_3) -> int) : {set Signs n}.
Admitted.

(* Definition signdet (n : nat) (taq : ('I_n -> 'I_3) -> int)  : *)
(*   {sa : {set Signs n} * {set Expos n} *)
(*         & 'M[int]_(#|sa.1|, #|sa.2|)}. *)
(* Proof. *)
(* elim: n taq. *)
(*   move=> taq; exists (set0, set0); exact 0. *)
(* move=> n' IHn taq. *)
(* set taq' := fun f => taq (fun (i : 'I_n'.+1) => *)
(*                  if (i < n')%N =P true is ReflectT P *)
(*                    then f (Ordinal P) else ord0). *)
(* have [[s a] /= M] := IHn taq'. *)
(* (* set s' := cnonnull s (row_mx (tvec taq (extset ord0 a)) *) *)
(* (*                  (row_mx (tvec taq (extset (1%R : 'F_3) a)) (tvec taq (extset (2%:R : 'F_3) a))) *m  *) *)
(* (*                castmx (mul3n _, erefl) (invmx (M *t ctmat1))). *) *)

(* (*  := *) *)
(* (*   match n with *) *)
(* (*     | 0     => (existT (fun sa : {set Signs n} * {set Expos n} *) *)
(* (*                          => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R) *) *)
(* (*     | n'.+1 =>  *) *)
(* (*       let taq' (f : 'I_n' -> 'I_3) :=  *) *)
(* (*           taq (fun (i : 'I_n) =>  *) *)
(* (*                  if (i < n')%N =P true is ReflectT P *) *)
(* (*                    then f (Ordinal P) else ord0) in *) *)
(* (*       let: existT (s, a) M := signdet taq' in *) *)
(* (*       let c := cnonnull s (row_mx (tvec taq (extset ord0 a)) *) *)
(* (*                  (row_mx (tvec taq (extset 1%R a)) (tvec taq (extset 2%R a))) *m  *) *)
(* (*                castmx (mul3n _, erefl) (invmx (M *t ctmat1))) in *) *)



(* (*       (* let s' :=  (extset 0%R s) :|: (extset 1%R s) :|: (extset 2%R s) in *) *) *)
(* (*       (* let a' :=  (extset 0%R a) :|: (extset 1%R a) :|: (extset 2%R a) in *) *) *)


(* (*  (existT (fun sa : {set Signs n} * {set Expos n} *) *)
(* (*                          => 'M[int]_(#|sa.1|, #|sa.2|)) (set0, set0) 0%R) *) *)
(* (*   end. *) *)

(* Admitted. *)

(* Definition signdetS (n : nat) (taq : ('I_n -> 'I_3) -> int) := *)
(*   let: existT sa _ := signdet taq in sa.1. *)

(* Definition signdetAda (n : nat) (taq : ('I_n -> 'I_3) -> int) := *)
(*   let: existT sa _ := signdet taq in sa.2. *)

(* Definition signdetM_subdef (n : nat) (taq : ('I_n -> 'I_3) -> int) : *)
(*   'M[int]_(#|signdetS taq|,#|signdetAda taq|). *)
(* Admitted. *)

(* Lemma signdet_sizeP (n : nat) (taq : ('I_n -> 'I_3) -> int) : *)
(*   #|signdetS taq| = #|signdetAda taq|. *)
(* Proof. *)
(* Admitted. *)

(* Definition signdetM  (n : nat) (taq : ('I_n -> 'I_3) -> int) : *)
(*   'M[int]_(#|signdetS taq|,#|signdetS taq|) := *)
(*   castmx (erefl, esym (signdet_sizeP taq)) (signdetM_subdef taq). *)

(* Lemma unit_signdet  (n : nat) (taq : ('I_n -> 'I_3) -> int) : *)
(*   signdetM taq \in unitmx. *)
(* Proof. *)
(* Admitted. *)


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