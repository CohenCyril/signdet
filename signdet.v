Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice path fintype finset finfun.
Require Import div bigop ssralg poly polydiv ssrnum perm zmodp ssrint rat tuple.
Require Import interval matrix (* mxtens  *) mxalgebra binomial.
Require Import path.

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

Lemma insubd_id (X : Type) (P : pred X) (S : subType P) (x y : S) :
  insubd x (val y) = y.
Proof. by apply: val_inj; rewrite insubdK //; apply: valP. Qed.

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

Lemma leqif_eq n m C : n <= m ?= iff C -> C -> n = m.
Proof. by case: C => [[_ /eqP]|//]. Qed.

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

Lemma extelt_small (X : finType) (x : X) n (i : 'I_n.+1)
  (b : X ^ n) (lt_in : i < n) :
  (extelt x b) i = b (Ordinal lt_in).
Proof.
rewrite ffunE; case: unliftP=> [j|] i_def; last first.
  by suff: false by []; rewrite i_def ltnn in lt_in *.
by congr (b _); apply: val_inj; rewrite /= i_def /= bump_small.
Qed.

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

Definition Xi n (X : finType) (S : {set X ^ n.+1}) (m : nat) :=
  [set s : X ^ n | [exists E : {set X}, (#|E| == m)
                   && [forall x in E, extelt x s \in S]]].

Lemma restrictP n (X : finType) (S : {set X ^ n.+1})
      (x : X ^ n.+1) (y : X ^ n) :
  reflect (exists i, x = extelt i y) (restrict x == y).
Proof.
apply: (iffP eqP) => [<-|[i ->]]; last by rewrite exteltK.
by exists (x ord_max); rewrite restrictK.
Qed.

Lemma restrict_in n (X : finType) (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> restrict s \in Xi S 1.
Proof.
move=> sS; rewrite inE; apply/existsP; exists [set s ord_max].
rewrite cards1 eqxx /=; apply/'forall_implyP => x.
by rewrite inE => /eqP ->; rewrite restrictK.
Qed.

Definition exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) :=
  [set (x : X ^ n.+1) ord_max | x in S & restrict x == s].

Lemma extsP (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) (x : X) :
  (x \in exts S s) = (extelt x s \in S).
Proof.
apply/imsetP/idP => /= [[xn]|xsS].
  by rewrite inE => /andP [xnS /eqP <-] ->; rewrite restrictK.
by exists (extelt x s); rewrite ?extelt_ord_max // inE exteltK eqxx andbT.
Qed.

Lemma card_extsP (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) m :
  (s \in Xi S m) = (m <= #|exts S s|).
Proof.
rewrite inE; apply/existsP/idP => /=.
  move=> [A /andP [/eqP card_A /'forall_implyP extxsS]].
  rewrite -card_A subset_leq_card //.
  by apply/subsetP => a aA; rewrite extsP; apply: extxsS.
set E := exts _ _; move=> extsS_big.
have /set0Pn [A] : [set A : {set X} | A \subset E & #|A| == m] != set0.
  by rewrite -card_gt0 cards_draws bin_gt0.
rewrite inE => /andP [AsubE card_A]; exists A; rewrite ?card_A /=.
by apply/'forall_implyP => a aA; rewrite -extsP; apply: (subsetP AsubE).
Qed.

Lemma card_exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n) :
  #|exts S s| <= #|X|.
Proof. by rewrite subset_leq_card //; apply/subsetP. Qed.

Definition seqext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :=
  sort (fun m n : 'I_k => m <= n) (enum (exts S s)).

Lemma mem_seqext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  seqext S s =i exts S s.
Proof. by move=> i; rewrite mem_sort mem_enum. Qed.

Lemma size_seqext k n (S : {set 'I_k ^ n.+1}) (s : 'I_k ^ n) :
  size (seqext S s) = #|exts S s|.
Proof. by rewrite size_sort -cardE. Qed.

Definition nthext k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) (m : nat) :=
  nth ord0 (seqext S s) m.

Lemma nthextP k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) x :
  reflect (exists2 i, i < #|exts S s| & nthext S s i = x) (x \in exts S s).
Proof. by rewrite -mem_seqext -size_seqext; apply: nthP. Qed.

Lemma in_nthext k n (S : {set 'I_k.+1 ^ n.+1})
           (s : 'I_k.+1 ^ n) (i : nat) : i < #|exts S s| ->
   nthext S s i \in exts S s.
Proof. by move=> i_small; apply/nthextP; exists i. Qed.

Lemma nthext_inj k n (S : {set 'I_k.+1 ^ n.+1}) (s : 'I_k.+1 ^ n) :
  {in [pred i | i < #|exts S s|] &, injective (nthext S s)}.
Proof.
move=> i j; rewrite !inE => i_small j_small /eqP.
by rewrite nth_uniq ?size_sort -?cardE ?sort_uniq ?enum_uniq => // /eqP.
Qed.

Lemma nthext_in k n (S : {set 'I_k.+1 ^ n.+1})
           (m : nat) (s : 'I_k.+1 ^ n) :
   s \in Xi S m -> forall i, i < m -> extelt (nthext S s i) s \in S.
Proof.
rewrite card_extsP => m_small i i_small.
by rewrite -extsP in_nthext // (leq_trans i_small).
Qed.

Lemma ord_max_in_exts (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> s ord_max \in exts S (restrict s).
Proof. by move=> sS; rewrite extsP restrictK. Qed.

Lemma exts_restrict_neq0 (X : finType) n (S : {set X ^ n.+1}) (s : X ^ n.+1) :
  s \in S -> exts S (restrict s) != set0.
Proof.
have [//|] := altP (set0Pn _); rewrite negbK => /eqP extsrs_eq0 sS.
by have := ord_max_in_exts sS; rewrite extsrs_eq0 inE.
Qed.

Definition reext k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat)  :=
  [set extelt (nthext S s m) s | s in Xi S m.+1].

Lemma card_reext k n (S : {set 'I_k.+1 ^ n.+1}) (m : nat) :
  #|reext S m| = #|Xi S m.+1|.
Proof.
rewrite card_in_imset //= => x y xXi yXi /eqP.
by rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma Xi_monotonic n (X : finType) (S S' : {set X ^ n.+1}) m :
  S \subset S' -> Xi S m \subset Xi S' m.
Proof.
move=> /subsetP subSS'; apply/subsetP => /= s; rewrite !in_set.
move=> /existsP /= [xs /andP[uxs /'forall_implyP /= HS]].
apply/existsP; exists xs; rewrite uxs //=.
by apply/'forall_implyP => /= x xxs; rewrite subSS' ?HS.
Qed.

Lemma leq_Xi n (X : finType) (S : {set X ^ n.+1}) :
  {homo Xi S : m p / (p <= m)%N >-> m \subset p}.
Proof.
move=> m p /= lpm; apply/subsetP => /= s.
rewrite !in_set => /existsP [/= E /andP [/eqP cardE /'forall_implyP /= inS]].
have /set0Pn [A] : [set A : {set X} | A \subset E & #|A| == p] != set0.
  by rewrite -card_gt0 cards_draws bin_gt0 cardE.
rewrite inE => /andP [AsubE cardA]; apply/existsP; exists A; rewrite cardA.
by apply/forallP => x; apply/implyP => /(subsetP AsubE); apply: inS.
Qed.

Lemma reext_inj k n (S : {set 'I_k.+1 ^ n.+1}) :
  {in [pred m | Xi S m.+1 != set0] &, injective (reext S)}.
Proof.
move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0.
have [// ? ?|neq_ij] := altP (i =P j).
wlog lt_ji : i j Xii_neq0 Xij_neq0 neq_ij / j < i => [hwlog|].
  have := neq_ij; rewrite neq_ltn => /orP [|/hwlog]; last exact.
  move=> /hwlog hwlogji eqXij; symmetry.
  by apply: hwlogji; rewrite // 1?eq_sym.
have /set0Pn [s sXi]:= Xij_neq0.
pose f k s := extelt (nthext S s k) s.
move=> /setP /(_ (f j s)); rewrite (mem_imset (f j) sXi).
move=> /imsetP [s' s'Xi] /eqP; rewrite eq_extelt andbC => /andP [/eqP->].
rewrite (inj_in_eq (@nthext_inj _ _ _ _)) ?inE -?card_extsP // => [/eqP //|].
by apply: subsetP s'Xi; rewrite leq_Xi // ltnS ltnW.
Qed.

Lemma reext_eq0 k n (S : {set 'I_k.+1 ^ n.+1}) m :
  (reext S m == set0) = (Xi S m.+1 == set0).
Proof. by rewrite -!cards_eq0 card_reext. Qed.

Lemma Xi0 n (X : finType) i : i > 0 -> @Xi n _ (set0 : {set X ^ n.+1}) i = set0.
Proof.
case: i => // i _; apply/setP => /= e; rewrite !inE /=.
apply: negbTE; rewrite negb_exists; apply/forallP => /= S.
have [[x xS]|] := altP (set0Pn S); last first.
  by rewrite negbK => /eqP ->; rewrite cards0.
apply/nandP; right; rewrite negb_forall; apply/existsP; exists x.
by rewrite xS inE.
Qed.

Lemma Xi1_eq0 n (X : finType) (S : {set X ^ n.+1}) :
  (Xi S 1 == set0) = (S == set0).
Proof.
apply/idP/idP=> [|/eqP->]; last by rewrite Xi0.
apply: contraTT => /set0Pn [x xS].
by apply/set0Pn; exists (restrict x); apply: restrict_in.
Qed.

Lemma reext0 k n m : @reext k n set0 m = set0.
Proof.
apply/setP=> i; rewrite !inE; apply/negP => /imsetP /= [x].
by rewrite Xi0 ?inE.
Qed.

Definition Signs n := ('I_3 ^ n)%type.
Definition Expos n := ('I_3 ^ n)%type.

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

Lemma card_extset (X : finType) n (S : {set X ^ n}) (x : X) :
  #|extset x S| = #|S|.
Proof.
by rewrite card_imset // => u v /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

Lemma ExposE n (S : {set Expos n.+1}) :
  S = \bigcup_(i < 3 | Xi S i.+1 != set0) reext S i.
Proof.
suff cover_S : S = \bigcup_(i < 3) reext S i.
  rewrite [LHS]cover_S.
  rewrite (bigID (fun i : 'I__ => Xi S i.+1 == set0)) /=.
  by rewrite big1 ?set0U // => i; rewrite -reext_eq0 => /eqP.
apply/setP => s; apply/idP/bigcupP => [sS|]; last first.
  move=> [i _ /imsetP [x x_in ->]].
  by rewrite (nthext_in x_in).
have /nthextP [i i_small ext_i] := ord_max_in_exts sS.
have Hi : i < 3.
  by rewrite (leq_trans i_small) // (leq_trans (card_exts _ _)) ?card_ord.
exists (Ordinal Hi) => //; apply/imsetP => /=.
exists (restrict s) => /=; first by rewrite card_extsP.
by rewrite ext_i restrictK.
Qed.

Lemma partition_Signs n (S : {set Signs n.+1}) :
  partition [set reext S (i : 'I__) | i in 'I_3 & Xi S i.+1 != set0] S.
Proof.
apply/and3P; split; [apply/eqP| |].
- symmetry; rewrite cover_imset [LHS]ExposE.
  by apply: eq_bigl => /= i; rewrite inE.
- apply/trivIsetP => /= _ _ /imsetP [i Xii_neq0 ->] /imsetP [j Xij_neq0 ->].
  rewrite !inE in Xii_neq0 Xij_neq0.
  rewrite (inj_in_eq (@reext_inj _ _ _)) ?inE //= => neq_ij.
  rewrite disjoints_subset; apply/subsetP => /= X /imsetP /= [x x_in ->].
  rewrite inE; apply/negP => /imsetP /= [y y_in] /eqP.
  rewrite eq_extelt andbC => /andP [/eqP eq_xy].
  rewrite -eq_xy {y eq_xy} in y_in *.
  rewrite (inj_in_eq (@nthext_inj _ _ _ _)) ?inE -?card_extsP //.
  exact/negP.
apply/negP=> /imsetP [i]; rewrite inE => /andP [j /set0Pn [x xXi]].
move=> /setP /(_ (extelt (nthext S x i) x)); rewrite !inE.
by rewrite (mem_imset (fun s => extelt (nthext S s i) s)).
Qed.

Lemma adapt0 n : @adapt n set0 = set0.
Proof.
elim: n => [|n IHn] //=; rewrite big1 // => i _.
by rewrite Xi0 // IHn extset0.
Qed.

Lemma adapt_eq0 n X : (@adapt n X == set0) = (X == set0).
Proof.
elim: n => [|n IHn] // in X *.
  apply/idP/idP => [/=|/eqP ->]; last by rewrite adapt0.
apply: contraTT; rewrite -Xi1_eq0 -IHn => /set0Pn [x x_adaX].
apply/set0Pn; exists (extelt ord0 x).
by apply/bigcupP; exists ord0 => //; rewrite mem_extset eqxx /=.
Qed.

Lemma partition_adapt n (S : {set Signs n.+1}) :
  partition [set extset i (adapt (Xi S (i : 'I_3).+1))
            | i in 'I_3 & Xi S i.+1 != set0] (adapt S).
Proof.
apply/and3P => /=; split; [apply/eqP | |].
- rewrite (bigID [pred i : 'I__ | Xi S i.+1 == set0]) /=.
  rewrite big1 ?set0U; last by move=> i /eqP ->; rewrite adapt0 extset0.
  by rewrite cover_imset; apply: eq_bigl => i; rewrite inE.
- apply/trivIsetP => /= _ _ /imsetP [i _ ->] /imsetP [j _ ->].
  rewrite eq_extset => /=.
  have [->|adX_neq0] /= := altP (_ =P set0).
    by rewrite extset0 -setI_eq0 set0I.
  have [<-|neq_ij _] /= := altP (i =P j); first by rewrite eqxx.
  rewrite disjoints_subset; apply/subsetP=> /= X /imsetP /= [Y Yin ->].
  by rewrite inE mem_extset (negPf neq_ij).
apply/negP=> /imsetP [i]; rewrite inE => Xi_neq0 /eqP.
by rewrite eq_sym extset_eq0 adapt_eq0; apply/negP.
Qed.

Lemma card_adapt n (S : {set Signs n}) : #|adapt S| = #|S|.
Proof.
elim: n => [//|n IHn] in S *.
rewrite (card_partition (partition_adapt S)).
rewrite (card_partition (partition_Signs S)).
rewrite !big_imset; last 2 first.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0 eq_reext_ij.
  by apply: val_inj; apply: (@reext_inj _ _ S); rewrite ?inE.
- move=> i j /=; rewrite !inE /= => Xii_neq0 Xij_neq0.
  move=> /eqP; rewrite eq_extset -cards_eq0 IHn cards_eq0 Xii_neq0 /=.
  by move=> /andP [/eqP ? _].
apply: eq_bigr => i _; rewrite card_extset IHn card_imset //=.
by move=> s t /= /eqP; rewrite eq_extelt => /andP [_ /eqP].
Qed.

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

Lemma enum_rank_in_id (T : finType) (x0 : T)
  (A : pred T) (Ax0 : x0 \in A) (x : T) :
  (enum_val (enum_rank_in Ax0 x) == x) = (x \in A).
Proof.
by apply/eqP/idP => [<-|xA]; rewrite ?enum_valP ?enum_rankK_in ?eqxx.
Qed.

Lemma rowfree_matP n (S : {set Signs n}) (E : {set Expos n}) :
  S != set0 -> E != set0 ->
  reflect (forall v : {ffun Signs n -> rat},
          (forall e : Expos n, e \in E ->
          (\sum_(s in S) v s * mat_coef s e = 0)%R) ->
            forall s : Signs n, s \in S -> v s = 0%R)
          (row_free (mat S E)).
Proof.
move=> /set0Pn /sigW [s0 s0S] /set0Pn /sigW [e0 e0E].
apply: (iffP idP) => [/row_freeP [M MP] v vP s sS|].
  have := MP.
  move=> /(congr1 (mulmx (\row_(i < #|S|) v (enum_val i)))).
  rewrite mulmxA mulmx1 => /rowP /(_ (enum_rank_in sS s)).
  rewrite !mxE enum_rankK_in // => <-.
  rewrite (reindex_onto (enum_rank_in e0E) enum_val) //=; last first.
    by move=> i; rewrite enum_valK_in.
  rewrite (eq_bigl _ _ (enum_rank_in_id _)).
  rewrite big1 => //= e _; rewrite !mxE.
  rewrite (reindex_onto (enum_rank_in sS) enum_val) //=; last first.
    by move=> i; rewrite enum_valK_in.
  rewrite (eq_bigl _ _ (enum_rank_in_id _)).
  pose e' := enum_val (enum_rank_in e0E e).
  have e'E : e' \in E by apply: enum_valP.
  set x := (X in (X * _)%R); suff -> : x = 0%R by rewrite mul0r.
  rewrite -[RHS](vP e') //; apply: eq_bigr => s' s'S.
  by rewrite !mxE -/e' enum_rankK_in.
move=> matcoefP.
suff: forall (L : 'rV__), L *m mat S E = 0%R -> L = 0%R.
  move=> Hmat; rewrite -kermx_eq0; apply/eqP.
  apply/row_matrixP => i; rewrite row0; apply/Hmat.
  by apply/sub_kermxP; rewrite row_sub.
move=> L.
pose v := [ffun s : Signs n => L ord0 (enum_rank_in s0S s)].
have -> : L = \row_i v (enum_val i).
  by apply/rowP => i; rewrite !mxE ffunE enum_valK_in.
move=> vM_eq0; apply/rowP => i; rewrite !mxE.
apply: matcoefP => //; last exact: enum_valP.
move=> e eE; have /rowP /(_ (enum_rank_in eE e)):= vM_eq0; rewrite !mxE.
rewrite (reindex_onto (enum_rank_in s0S) enum_val) //=; last first.
  by move=> j; rewrite enum_valK_in.
rewrite (eq_bigl _ _ (enum_rank_in_id _)) => S_eq0; rewrite -[RHS]S_eq0.
apply: eq_bigr => s sS; rewrite !mxE.
by rewrite !enum_rankK_in.
Qed.

Definition ffun0 (T : finType) (X : Type) : #|T| = 0 -> {ffun T -> X}.
Proof. by move=> /card0_eq T0; apply: finfun => t; move: (T0 t). Defined.

Lemma adapt_adapted n (S : {set Signs n}) : adapted S (adapt S).
Proof.
rewrite /adapted {1}card_adapt eqxx /=.
have [->|SN0] := altP (S =P set0).
  by move: (mat _ _); rewrite cards0 => M; rewrite flatmx0 -row_leq_rank.
apply/rowfree_matP; rewrite ?adapt_eq0 // {SN0}.
elim: n => [|n IHn] in S *.
  move=> v vP s sS; have card30 : #|{: 'I_3 ^ 0}| = 1.
    by rewrite card_ffun !card_ord expn0.
  have /= := (vP s); rewrite sS => /(_ isT); have -> : S = [set s].
    by apply/setP => x; rewrite !(fintype1 s) // !inE eqxx.
  by rewrite big_set1 /mat_coef big_ord0 mulr1.
move=> v vP s sS.
pose v' i := [ffun x => v (extelt i x)].
suff v's_eq0 i : i \in exts S (restrict s) -> v' i (restrict s) = 0%R.
  admit.
move=> i_in.
apply: (IHn (Xi S i.+1)); last first.
  admit.
move=> e.
rewrite (set_partition_big _ (partition_Signs S)) /=.
rewri
  rewrite -cards_eq0. -card_exts.


  by move: (mat _ _); rewrite cards0 => M; rewrite flatmx0 -row_leq_rank.
apply/rowfree_matP; rewrite ?adapt_eq0 // => v vP s.
rewrite (set_partition_big _ (partition_adapt S)) /=.
rewrite (set_partition_big _ (partition_Signs S)) /=.




have [->|S_neq0] := eqVneq S set0.
  by move: (mat _ _); rewrite card_adapt !cards0.
have [] := @ex_maxnP (fun m => Xi S m.+1 != set0) 2.
- exists 0.
  have /set0Pn [s sS] := S_neq0.
  apply/set0Pn; exists (restrict s).
  rewrite inE; apply/existsP; exists [set s ord_max].
  rewrite cards1 eqxx /=; apply/'forall_implyP => i.
  by rewrite inE => /eqP ->; rewrite restrictK.
- move=> i; apply: contraNT.
  rewrite -ltnNge => i_big; apply/eqP/setP=> s; rewrite !inE.
  apply: negbTE; rewrite negb_exists; apply/forallP => E.
  rewrite negb_and ltn_eqF //= ltnS (leq_trans _ i_big) //.
  by rewrite (leq_trans (max_card _)) ?card_ord.
elim => [|M IHM] XiM_neq0 M_max.
  rewrite /= (bigD1 ord0) //= big1 ?setU0; last first.
    move=> i i_neq0.
    apply/eqP; rewrite extset_eq0 -cards_eq0 card_adapt cards_eq0.
    apply/negP=> /negP /M_max; rewrite leqn0; apply/negP.
    by rewrite -val_eqE in i_neq0.
  rewrite -(cover_partition (partition_Signs S)) cover_imset.
  rewrite (bigD1 ord0) ?inE //= big1 ?setU0; last first.
    by move=> i; rewrite !inE -!val_eqE /= => /andP [/M_max]; case: (val i).
  have := IHn (Xi S 1) => /=.


suff: forall (L : 'rV__), L *m mat S (adapt S') = 0%R ->  L = 0%R.
  move=> Hmat; rewrite -kermx_eq0; apply/eqP.
  apply/row_matrixP => i; rewrite row0; apply/Hmat.
  by apply/sub_kermxP; rewrite row_sub.
move=> L LP.
have: (\sum_(i < #|S|) (L ord0 i)%:M *m
  \row_(j < #|adapt S'|) mat_coef (enum_val i) (enum_val j) = 0)%R.
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
rewrite (set_partition_big _ (partition_Signs S)) /=.
rewrite -(cover_partition (partition_Signs S)) cover_imset  in S_neq0 L LP s0S *.



have [] := @ex_maxnP (fun m => Xi S m.+1 != set0) 2.
- exists 0.
  have /set0Pn [s sS] := S_neq0.
  apply/set0Pn; exists (restrict s).
  rewrite inE; apply/existsP; exists [set s ord_max].
  rewrite cards1 eqxx /=; apply/'forall_implyP => i.
  by rewrite inE => /eqP ->; rewrite restrictK.
- move=> i; apply: contraNT.
  rewrite -ltnNge => i_big; apply/eqP/setP=> s; rewrite !inE.
  apply: negbTE; rewrite negb_exists; apply/forallP => E.
  rewrite negb_and ltn_eqF //= ltnS (leq_trans _ i_big) //.
  by rewrite (leq_trans (max_card _)) ?card_ord.
elim => [|M IHM] XiM_neq0 M_max.
  rewrite (bigD1 ord0) //= big1 ?setU0; last first.
    move=> i i_neq0.
    apply/eqP; rewrite extset_eq0 -cards_eq0 card_adapt cards_eq0.
    apply/negP=> /negP /M_max; rewrite leqn0; apply/negP.
    by rewrite -val_eqE in i_neq0.
  rewrite -(cover_partition (partition_Signs S)) cover_imset.
  rewrite (bigD1 ord0) ?inE //= big1 ?setU0; last first.
    by move=> i; rewrite !inE -!val_eqE /= => /andP [/M_max]; case: (val i).


  rewrite /mat.

    apply/eqP; rewrite extset_eq0 -cards_eq0 card_adapt cards_eq0.
    apply/negP=> /negP /M_max; rewrite leqn0; apply/negP.
    by rewrite -val_eqE in i_neq0.



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


Definition nonEmptySigns n (taq : ('I_n -> 'I_3) -> int) : {set Signs n}.
Admitted.

End SignDet.