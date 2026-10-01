#import "main-defs.typ": Aff, E, GL, K, SK, SL, U, det, source, symbol-idx
#import "statements.typ": condition-item, condition-list, proof, theorem

#heading(level: 2)[Нормальные делители группы $GL(A)$; группы
  $K_1 (A, frak(q))$]
<sec:normal-subgroups-relative-k1>

#theorem[
  Пусть $A$~— кольцо.
  #condition-list[
    #condition-item(format: "cyrillic")[Если $H subset GL(A)$~— подгруппа,
      нормализуемая группой $E(A)$, то существует, и притом единственный,
      двусторонний идеал $frak(q)$ кольца $A$, такой, что $H$ является
      подгруппой уровня $frak(q)$, т.~е. что
      $E(A, frak(q)) subset H subset GL(A, frak(q))$.]
    <cond:stable-linear-normalized-subgroup-level>

    #condition-item(format: "cyrillic")[Пусть $frak(q)$~— двусторонний идеал
      кольца $A$, и пусть $H subset GL(A)$~— подгруппа уровня $frak(q)$. Тогда
      $
        E(A, frak(q)) = [E(A), H] = [GL(A), H] quad (subset H).
      $
    ] <cond:stable-linear-relative-commutators>

    #condition-item(format: "cyrillic")[Пусть $f: A -> B$~— сюръективный
      гомоморфизм колец, $H$~— подгруппа, удовлетворяющая предположениям
      п.~@cond:stable-linear-relative-commutators. Тогда отображение
      $E(A, frak(q)) -> E(B, f(frak(q)))$ сюръективно и $f(H)$ является
      нормальным делителем уровня $f(frak(q))$ группы $GL(B)$.]
    <cond:stable-linear-level-quotient-surjection>
  ]
] <th:stable-linear-normal-subgroups>

#source(189)Эта теорема показывает, что для любого двустороннего идеала
$frak(q)$ группа
$
  K_1 (A, frak(q)) eq.def GL(A, frak(q)) slash E(A, frak(q))
$#symbol-idx($K_1 (A, frak(q))$, sort: "K_1(A,q)", group: "groups", order: 107)
является абелевой группой. Кроме того, _описание групп $K_1 (A, frak(q))$ для
всех $frak(q)$ равносильно описанию всех нормальных делителей группы
$GL(A)$_. В гл.~@ch:projective-k-theory группы $K_1 (A, frak(q))$ возникнут по
другому поводу, но будет показана эквивалентность двух определений этих групп.

В том случае, когда кольцо $A$ коммутативно, можно рассмотреть отображение
$det: GL(A) -> U(A)$, ядро $SL(A)$ которого содержит $[GL(A), GL(A)] = E(A)$.
Следовательно, для каждого идеала $frak(q)$ возникает расщепляющаяся точная
последовательность
$
  0 -> SK_1 (A, frak(q)) -> K_1 (A, frak(q)) arrow.r^det
  U(A, frak(q)) -> 0,
$
где
$
  SK_1 (A, frak(q)) = SL(A, frak(q)) slash E(A, frak(q)).
$#symbol-idx(
  $SK_1 (A, frak(q))$,
  sort: "SK_1(A,q)",
  group: "groups",
  order: 119,
)
Приведенная теорема показывает к тому же, что группы $SK_1 (A, frak(q))$
классифицируют нормальные делители группы $SL(A)$.

Если $frak(q) = A$, то положим
$
  K_1 (A) = K_1 (A, A) = GL(A) slash E(A),
$
и если кольцо $A$ коммутативно, то определим
$
  SK_1 (A) = SK_1 (A, A) = SL(A) slash E(A).
$

#proof(head: [Доказательство теоремы @th:stable-linear-normal-subgroups.])[
  Часть @cond:stable-linear-level-quotient-surjection непосредственно следует из
  @prop:elementary-matrices-quotient-surjection и
  п.~@cond:stable-linear-normalized-subgroup-level,
  @cond:stable-linear-relative-commutators настоящей теоремы. Для
  @cond:stable-linear-relative-commutators достаточно показать, что
  $
    E(A, frak(q)) = [E(A), E(A, frak(q))] = [GL(A), GL(A, frak(q))].
  $
  Первое равенство вытекает из следствия @cor:relative-elementary-commutators.
  Во втором равенстве включение $subset$ очевидно. Значит, достаточно показать,
  что $[GL(A), GL(A, frak(q))] subset E(A, frak(q))$. Но это следует из
  @cor:linear-commutator-doubled-rank, если перейти к пределу.

  Остается доказать @cond:stable-linear-normalized-subgroup-level.
  Единственность идеала $frak(q)$ следует из замечания
  @eq:congruence-subgroup-unique-level в
  §~@sec:elementary-matrices-congruence-subgroups (или из
  @cond:stable-linear-relative-commutators).

  Покажем сначала, что если $H != {I}$, то $E(A, frak(q)) subset H$ для
  некоторого ненулевого идеала $frak(q)$. Действительно, пусть
  $H_n = H inter GL_n (A)$. Будем рассматривать $H_n$ как подгруппу группы
  $
    mat(GL_n (A), A^n; 0, I) subset GL_(n + 1) (A),
  $
  которая сопряжена с аффинной группой $Aff_n (A)$ (см.
  §~@sec:affine-module-group гл.~@ch:stable-projective-structure). Подгруппа
  $H_n$ нормализуется группой $E_n (A)$, и $H_n != {I_n}$ для #source(
    190,
  )достаточно большого $n$. Следовательно, из (@prop:affine-subgroup-commutators
  @cond:affine-commutator-image и @cond:affine-invariant-ideals) вытекает, что
  $[H_n, A^n] = A^n frak(a)$ для некоторого ненулевого левого идеала
  $frak(a) subset A$, т.~е. $[H_n, A^n] subset H$ состоит из всех матриц
  $mat(I_n, x; 0, I)$, у которых все элементы строчки $x in A^n$ лежат в
  $frak(a)$. Из следствия @cor:elementary-level-containment теперь вытекает, что
  $E(A, frak(a) A) subset H$, и тем самым доказано сформулированное утверждение.

  Для завершения доказательства теоремы предположим, что $frak(q)$~— наибольший
  двусторонний идеал кольца $A$, для которого $E(A, frak(q)) subset H$
  (очевидно, такой существует). Покажем, что $H subset GL(A, frak(q))$. Если это
  не так, то пусть $H'$~— образ подгруппы $H$ в $GL(A')$, где
  $A' = A slash frak(q)$. Так как отображение $E(A) -> E(A')$ сюръективно, то
  подгруппа $H'$ нормализуется группой $E(A')$. Поскольку $H' != {I}$, то из
  последнего абзаца следует, что $E(A', frak(q)' slash frak(q)) subset H'$ для
  некоторого идеала $frak(q)' != frak(q)$. Переходя к прообразу, получаем, что
  $E(A, frak(q)') subset GL(A, frak(q)) dot H$. Следовательно,
  $
    E(A, frak(q)') = [E(A), E(A, frak(q)')]
    subset [E(A), GL(A, frak(q)) dot H].
  $
  Если $epsilon in E(A)$, $alpha in GL(A, frak(q))$ и $beta in H$, то
  $[epsilon, alpha beta] = [epsilon, beta] [epsilon, alpha]^beta$ (см.
  @ss:group-commutator-identities). Так как группа $E(A)$ нормализует $H$, то
  $[epsilon, beta] in H$. Кроме того, в силу утверждения
  @cond:stable-linear-relative-commutators,
  $[epsilon, alpha] in E(A, frak(q)) subset H$. Следовательно,
  $[epsilon, alpha beta] in H$, и это показывает, что $E(A, frak(q)') subset H$.
  Тем самым возникает противоречие с максимальностью идеала $frak(q)$. Теорема
  доказана.
]
