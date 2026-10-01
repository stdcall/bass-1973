#import "main-defs.typ": (
  Aut, Hom, Im, U, fRank, idx, moduleCategory, rad, source, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition,
)

== Проективные модули над полулокальными кольцами
<sec:semilocal-projective-modules>

Зафиксируем в этом параграфе кольцо $A$ с радикалом $J = rad A$. Иногда мы будем
предполагать, что кольцо $A$ полулокально, т.~е. что $A/J$ — полупростое кольцо.

Пусть $P in moduleCategory hyph A$ и $alpha in P$. Введем обозначения
$
  P^* = Hom_A (P, A),
$
#symbol-idx($P^*$, sort: "superscript *", group: "superscripts", order: 149)
$
  o_P (alpha) = {h alpha | h in P^*}.
$
#symbol-idx($o_P (alpha)$, sort: "o_p(α)", group: "groups", order: 113)
Последнее множество является левым идеалом.

#source(142)Назовем элемент $alpha$ _унимодулярным в_ $P$, если
$o_P (alpha) = A$.#idx("унимодулярный элемент") Очевидно, это эквивалентно тому,
что отображение $h: A -> P$ ($h(a) = alpha a$) является расщепляющимся
мономорфизмом.

#proposition[
  Пусть $sigma, tau: Q -> P$ — морфизмы в категории $moduleCategory hyph A$.
  Допустим, что $Q in bold(P)(A)$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[[ $sigma$ — расщепляющийся мономорфизм]
      $<=>$ [ $sigma^*: P^* -> Q^*$ —
      эпиморфизм];] <cond:split-monomorphism-dual-epimorphism>

    #condition-item(format: "cyrillic")[если $Im(sigma - tau) subset P J$, то [
      $sigma$ — расщепляющийся мономорфизм] $<=>$ [таким является
      $tau$].] <cond:split-monomorphism-radical-invariance>
  ]
] <prop:split-monomorphism-dual-radical>

#proof[
  @cond:split-monomorphism-dual-epimorphism Если $sigma$ обладает левым
  обратным, то $sigma^*$ обладает правым обратным и поэтому отображение
  $sigma^*$ сюръективно. Обратно, так как $Q^* in bold(P)(A^degree)$, то если
  $sigma^*$ — сюръективное отображение, $sigma^*$ обладает правым обратным.
  Следовательно, $sigma^(**) : Q^(**) -> P^(**)$ обладает левым обратным, скажем
  $sigma'$. Если $h_P: P -> P^(**)$ — каноническое отображение, то
  $h_Q^(-1) sigma' h_P$ — левый обратный для $sigma$.

  @cond:split-monomorphism-radical-invariance Включение
  $J Q^* subset Hom_A (Q, J)$, очевидно, превращается в равенство, когда
  $Q = A$, а следовательно, в силу аддитивности и тогда, когда
  $Q in bold(P)(A)$. Если $h in Im(sigma - tau)^*$, то $h(Q) subset J$, и в силу
  только что сделанного замечания $h in J Q^*$. Следовательно, отображения
  $sigma^*, tau^*: P^* -> Q^*$ совпадают по модулю $J Q^*$. Таким образом, из
  леммы Накаямы вытекает, что [отображение $sigma^*$ сюръективно] $<=>$
  [отображение $tau^*$ сюръективно]. Поэтому
  @cond:split-monomorphism-radical-invariance следует из
  @cond:split-monomorphism-dual-epimorphism. Предложение доказано.
]

С этого момента будем предполагать, что кольцо $A$ _полулокально_. Если
$P in moduleCategory hyph A$ и $S$ — подмножество в $P$, то через $(S)$
обозначим подмодуль в $P$, порожденный $S$. Определим
$
  fRank_A (S; P)
$
#symbol-idx($fRank$, sort: "f-rank", group: "operators", order: 49)
как точную верхнюю грань всех тех целых $r >= 0$, для которых $(S)$ содержит
прямое слагаемое модуля $P$, изоморфное $A^r$; это — неотрицательное целое число
(или бесконечность). Поскольку кольцо $A$ фиксировано, нижний индекс мы часто
будем опускать.

#proposition[
  $fRank(S; P) = fRank((S) + P J; P)$.
] <prop:free-rank-radical-invariance>

#proof[
  Очевидно, достаточно показать, что левая часть не меньше правой. Пусть
  $sigma: A^r -> P$ — расщепляющийся мономорфизм с $Im(sigma) subset (S) + P J$.
  Выберем $tau: A^r -> (S)$ так, чтобы $Im(sigma - tau) subset P J$. Тогда из
  @prop:split-monomorphism-dual-radical
  @cond:split-monomorphism-radical-invariance следует, что $tau$ —
  расщепляющийся мономорфизм.
]

#proposition[
  Пусть $P in moduleCategory hyph A$, и пусть $alpha, beta in P$ — унимодулярные
  элементы. Тогда найдется автоморфизм $phi in Aut_A (P)$, такой, что:
  #condition-list[
    #condition-item[$phi(alpha A) = beta A$;] <cond:semilocal-unimodular-image>
    #condition-item[$phi$ оставляет инвариантными все подмодули, содержащие
      $alpha$ и $beta$.] <cond:semilocal-unimodular-invariance>
  ]
] <prop:semilocal-unimodular-transitivity>

#source(143)
#proof[
  Записывая $P = beta A plus.o P'$ и $alpha = beta b + alpha_(P')$ ($b in A$,
  $alpha_(P') in P'$), видим, что $A = o_P (alpha) = A b + o_(P') (alpha_(P'))$.
  В силу @prop:semilocal-unit-in-coset найдется элемент
  $a in o_(P') (alpha_(P'))$, такой, что $u = b + a in U(A)$. Выберем
  $f' in (P')^*$ так, чтобы $a = f'(alpha_(P'))$, и определим $f: P -> P$,
  полагая $f(beta x + y) = beta f'(y)$ для $x in A$, $y in P'$. Тогда $f^2 = 0$,
  и поэтому $phi_1 = 1_P + f$ — автоморфизм, причем
  $phi_1 (alpha) = beta u + alpha_(P')$. Определим $g: P -> P$, полагая
  $g(beta x + y) = alpha_(P') u^(-1) x$. Опять $g^2 = 0$, и поэтому
  $phi_2 = 1_P - g$ — автоморфизм, причем $phi_2 phi_1 (alpha) = beta u$. Ясно,
  что автоморфизм $phi = phi_2 phi_1$ удовлетворяет условиям
  @cond:semilocal-unimodular-image и @cond:semilocal-unimodular-invariance.
]

#corollary[
  Предположим, что $P, P' in moduleCategory hyph A$ и $Q in bold(P)(A)$. Тогда
  $
    P plus.o Q tilde.eq P' plus.o Q => P tilde.eq P'.
  $
] <cor:semilocal-projective-cancellation>

#proof[
  Записывая $Q plus.o Q' tilde.eq A^n$ и применяя индукцию по $n$, сведем задачу
  к случаю $Q = A$. Итак, пусть имеет место равенство модулей
  $P plus.o alpha A = P' plus.o beta A$, где элементы $alpha$ и $beta$
  унимодулярны (мы отождествляем модули с помощью изоморфизма). Выберем
  автоморфизм $phi$, как в @prop:semilocal-unimodular-transitivity. Тогда
  $
    P tilde.eq (P plus.o alpha A)/(alpha A)
    tilde.eq (P plus.o alpha A)/phi(alpha A)
    = (P' plus.o beta A)/(beta A) tilde.eq P'.
  $
]

#corollary[
  Если $M$ — подмодуль модуля $P in moduleCategory hyph A$, то
  $
    fRank(A^r plus.o M; A^r plus.o P) = r + fRank(M; P).
  $
] <cor:semilocal-free-rank-additivity>

#proof[
  Левая часть, очевидно, не меньше правой. Для доказательства обратного
  неравенства достаточно (несложная индукция) рассмотреть случай, когда $r = 1$.
  Пусть $alpha_1, dots, alpha_s in beta A plus.o M$ — базис свободного прямого
  слагаемого модуля $beta A plus.o P$. Выберем $phi$, как в
  @prop:semilocal-unimodular-transitivity, относительно $alpha_1$ и $beta$.
  Тогда из условия @prop:semilocal-unimodular-transitivity
  @cond:semilocal-unimodular-invariance следует, что
  $phi(alpha_i) in beta A plus.o M$ для всех $i$. Кроме того, в силу
  @prop:semilocal-unimodular-transitivity @cond:semilocal-unimodular-image
  $beta A plus.o M = phi(alpha_1) A plus.o M$, и потому можно записать
  $phi(alpha_i) = phi(alpha_1) a_i + beta_i$, где $beta_i in M$ ($2 <= i <= s$).
  Теперь уже очевидно, что множество $beta_2, dots, beta_s$ является базисом
  свободного прямого слагаемого модуля $P$. Таким образом,
  $
    fRank(A plus.o M; A plus.o P) >= s => fRank(M; P) >= s - 1.
  $
]

#corollary[
  Пусть $P in moduleCategory hyph A$, и пусть $alpha$ и $S$ — соответственно
  элемент и подмножество модуля $P$. Тогда
  $
    fRank(S, alpha; P) <= 1 + fRank(S; P).
  $
] <cor:free-rank-one-generator-bound>

#proof[
  Отобразим $A plus.o P$ на $P$, отображая $A$ на $alpha A$. Расщепляющийся
  мономорфизм $sigma: A^n -> P$, образ которого принадлежит $alpha A + (S)$,
  можно поднять до гомоморфизма $sigma': A^n -> A plus.o P$ с образом в
  $A plus.o (S)$. Следовательно,
  $fRank(S, alpha; P) <= fRank(A plus.o (S); A plus.o P)$. Далее применим
  @cor:semilocal-free-rank-additivity.
]

#source(144)
#proposition[
  Пусть $P in moduleCategory hyph A$ и $alpha_1, dots, alpha_r in P$.
  Предположим, что $fRank(alpha_1, dots, alpha_r; P) >= t$ для некоторого
  $t < r$. Тогда найдутся элементы $beta_i = alpha_i + alpha_r a_i$ ($a_i in A$,
  $1 <= i <= t$), такие, что
  $fRank(beta_1, dots, beta_t, alpha_(t+1), dots, alpha_(r-1); P) >= t$.
] <prop:semilocal-free-rank-generator-reduction>

#proof[
  Проведем индукцию по $t$. Случай $t = 0$ тривиален.

  _Случай $t = 1$._ Выберем унимодулярный элемент
  $beta in (alpha_1, dots, alpha_r)$. Запишем $P = beta A plus.o Q$ и
  $alpha_i = beta b_i + alpha'_i$ ($b_i in A$, $alpha'_i in Q$, $1 <= i <= r$).
  Расписывая $beta = sum alpha_i c_i$, видим, что $sum b_i c_i = 1$. Применяя
  @prop:semilocal-unit-in-coset к $b_1 A + sum_(2 <= i <= r) b_i A = A$, можно
  разрешить уравнение $u = b_1 + sum_(i >= 2) b_i a_i in U(A)$. Следовательно,
  элемент
  $
    alpha = alpha_1 + sum_(i >= 2) alpha_i a_i
    = beta u + (alpha'_1 + sum_(i >= 2) alpha'_i a_i)
  $
  унимодулярен. Таким образом,
  $
    fRank(alpha_1 + alpha_r a_r, alpha_2, dots, alpha_(r-1); P) >= 1.
  $

  _Случай $t > 1$._ В силу @cor:free-rank-one-generator-bound
  $
    fRank(alpha_2, dots, alpha_r; P) >= t - 1.
  $
  Следовательно, проводя индукцию, найдем $beta_i = alpha_i + alpha_r a_i$
  ($2 <= i <= t$), такие, что
  $
    fRank(beta_2, dots, beta_t, alpha_(t+1), dots, alpha_(r-1); P) >= t - 1.
  $
  Пусть $P' subset (beta_2, dots, beta_t, alpha_(t+1), dots, alpha_(r-1))$ —
  прямое слагаемое модуля $P$, изоморфное модулю $A^(t-1)$. Запишем
  $P = P' plus.o P''$, $alpha_i = alpha'_i + alpha''_i$ и
  $beta_i = beta'_i + beta''_i$ в этом разложении. Тогда, используя
  @cor:semilocal-free-rank-additivity, получаем
  $
    t & <= fRank(alpha_1, dots, alpha_r; P) \
      & = fRank(alpha_1, beta_2, dots, beta_t, alpha_(t+1), dots, alpha_r; P) \
      & = fRank(
          P' plus.o (alpha''_1, beta''_2, dots, beta''_t,
            alpha''_(t+1), dots, alpha''_r); P' plus.o P''
        ) \
      & = (t - 1) + fRank(
          alpha''_1, beta''_2, dots, beta''_t,
          alpha''_(t+1), dots, alpha''_r; P''
        ).
  $
  Согласно разобранному случаю $t = 1$, можно найти элемент $a_1$, такой, что
  $
    fRank(
      alpha''_1 + alpha''_r a_1, beta''_2, dots, beta''_t,
      alpha''_(t+1), dots, alpha''_(r-1); P''
    ) >= 1.
  $
  Если положить $beta_1 = alpha_1 + alpha_r a_1$, то элементы
  $beta_1, dots, beta_t$, очевидно, дадут решение нашей задачи.
]
