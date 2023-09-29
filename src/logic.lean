
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_contradiction hboom,
  have b : false := p hboom,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
-- caso → 
  intro p,
  by_contradiction hboom,
  have b : false := p hboom,
  contradiction,
-- caso ← 
  intro h,
  intro hb,
  have b : false := hb h,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p,
  cases p,
  right,
  exact p,
  left,
  exact p,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p,
  split,
  cases p,
  exact p_right,
  cases p,
  exact p_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro p,
  intro h,
  cases p,
  have b : false := p h,
  contradiction,
  exact p,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro fp, --f(alse)p
  cases pq,
  have b : false := fp pq,
  contradiction,
  exact pq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro fq, -- f(alse)q
  intro p,
  have b : Q := pq p,
  have c : false := fq b,
  exact c,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro fqfp, -- f(alse)q and f(alse)p
  intro p,
  by_contradiction hboom,
  have b : ¬P  := fqfp hboom,
  have c : false := b p,
  exact c,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
--caso → 
  intro pq,
  intro fq,
  intro p,
  have b : Q := pq p,
  have c : false := fq b,
  exact c,
--caso ← 
  intro fqfp,
  intro p,
  by_contradiction hboom,
  have b : ¬P  := fqfp hboom,
  have c : false := b p,
  exact c,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro f_pfp, -- f(p or fp)
  have b : (P ∨ ¬P),
  right,
  intro p,
  have c : (P ∨ ¬P),
  left,
  exact p,
  have d : false := f_pfp c,
  contradiction,
  have e : false := f_pfp b,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro fp,
  have b : (P → Q),
  intro p,
  have c : false := fp p,
  contradiction,
  have d : P := pqp b,
  have e : false := fp d,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro fpfq,
  cases fpfq with l r,
  cases pq,
  have b : false := l pq,
  contradiction,
  have c : false := r pq,
  contradiction, 
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro fpfq,
  cases pq with p q,
  cases fpfq with fp fq,
  have b : false := fp p,
  contradiction,
  have c : false := fq q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro f_pq,
  split,
  intro p,
  have b : (P ∨ Q),
  left,
  exact p,
  have c : false := f_pq b,
  contradiction,
  intro q,
  have b : (P ∨ Q),
  right,
  exact q,
  have c : false := f_pq b,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro fpfq,
  intro pq,
  cases fpfq with fp fq,
  cases pq with p q,
  -- caso p
  have b : false := fp p,
  contradiction,
  --caso q
  have c : false := fq q,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro f_pq,
  by_cases p : P,
  left,
  intro q,
  have pq : (P ∧ Q),
  split,
  exact p,
  exact q,
  apply f_pq,
  exact pq,
  right,
  exact p,  
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro fqfp,
  intro qp,
  cases qp with p q,
  cases fqfp with fq fp,
  apply fq,
  exact q,
  apply fp,
  exact p,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  cases qr with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split, 
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
  split,
  exact p,
  left,
  exact q,
  cases pr with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  cases pqr with p qr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qr with q r,
  split,
  right,
  exact q,
  right, 
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr with pq pr,
  cases pq with p q,
  left,
  exact p,
  cases pr with p r,
  left, 
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  have pq : (P ∧ Q),
  split,
  exact p,
  exact q,
  have r : R := pqr pq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pqr,
  intro pq,
  cases pq with p q,
  have r : R := pqr p q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  intro p,
  split, 
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro fpx,
  intro x,
  intro px,
  apply fpx,
  existsi x,
  exact px,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro afpx, --all false P x
  intro epx, --exist P x
  cases epx with t ht,
  exact afpx t ht,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro fapx,
  by_contradiction h1,
  apply fapx,
  intro x,
  by_contradiction h2,
  apply h1,
  existsi x,
  exact h2,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro efpx,
  intro apx,
  cases efpx with x hx,
  apply hx,
  exact apx x,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro epx,
  intro afpx,
  cases epx with x px,
  have k:= afpx(x),
  apply k,
  exact px,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro apx,
  intro efpx, --false exist false P x
  cases efpx with x fpx,
  have k:= apx(x),
  apply fpx,
  exact k,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro fefpx,
  intro x,
  by_contra,
  apply fefpx,
  existsi x,
  exact h,
  
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro fapx,
  by_contra,
  apply fapx,
  intro x,
  intro px,
  apply h,
  existsi x,
  exact px,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro epxqx,
  split,
  cases epxqx with x pxqx,
  cases pxqx with px qx,
  existsi x,
  exact px,
  cases epxqx with x pxqx,
  cases pxqx with px qx,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro epxqx,
  cases epxqx with x pxqx,
  cases pxqx with px qx,
  left,
  existsi x,
  exact px,
  right,
  existsi x,
  exact qx,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro epxoeqx, --exist P x or exist Q x
  cases epxoeqx with px qx,
  cases px with x px,
  existsi x,
  left,
  exact px,
  cases qx with x qx,
  existsi x,
  right,
  exact qx,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro apxqx,
  split,
  intro x,
  have h:= apxqx(x),
  cases h with px qx,
  exact px,
  intro x,
  have h:= apxqx(x),
  cases h with px qx,
  exact qx,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  cases h with apx aqx,
  intro x,
  split,
  have px := apx(x),
  exact px,
  have qx := aqx(x),
  exact qx,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro x,
  cases h with px qx,
  left,
  have px := px(x),
  exact px,
  right,
  have qx := qx(x),
  exact qx,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
