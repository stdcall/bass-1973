#import "main-defs.typ": (
  colim, hd, idx, moduleCategoryOf, rtGlDim, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition, theorem,
)

== Теорема Гильберта о сизигиях <sec:hilbert-syzygy-theorem>

#source(482)#idx("теорема Гильберта о сизигиях")Теорема утверждает, что
$rtGlDim A[t] = 1 + rtGlDim A$ (см. @th:hilbert-syzygy-global-dimension).

#proposition(title: [Капланский])[
  #idx("теорема Капланского")Пусть $B$ — кольцо, $A = B/(t B)$, где $t$ —
  элемент из центра кольца $B$, не являющийся при этом делителем нуля в $B$.
  Если $M in moduleCategoryOf(A)$, $M != 0$ и $hd_A (M) = n < infinity$, то
  $hd_B (M) = n + 1$.
] <prop:kaplansky-central-quotient-dimension>

#proof[
  Из точности последовательности $0 -> B arrow.r^t B -> A -> 0$ следует, что
  $hd_B (P) <= 1$ для проективного $A$-модуля $P$. Если $P != 0$, то должно
  иметь место равенство, поскольку ввиду $P t = 0$ модуль $P$ не может быть
  $B$-проективным. Пусть теперь $n > 0$ и $0 -> N -> P -> M -> 0$, где $P$ —
  $A$-проективный модуль. Тогда $N != 0$, $hd_A (N) = n - 1$. По индуктивному
  предположению $hd_B (N) = n$ и $hd_B (P) = 1$. Из
  @prop:projective-dimension-sequence следует, что $hd_B (M) <= n + 1$ (с
  равенством при $n > 1$).

  Если $n = 1$, то запишем $M$ в виде $M = Q/H$, где $Q$ — $B$-проективный
  модуль. Тогда точны следующие последовательности $A$-модулей:
  $ 0 -> H/(Q t) -> Q/(Q t) -> M -> 0, $
  $ 0 -> (Q t)/(H t) -> H/(H t) -> H/(Q t) -> 0. $
  Из $A$-проективности модуля $Q/(Q t)$ следует проективность $A$-модуля
  $H/(Q t)$ (так как $n = 1$). Отсюда следует расщепляемость второй
  последовательности. Таким образом, $M tilde.eq (Q t)/(H t)$ является прямым
  слагаемым в $H/(H t)$. Следовательно, модуль $H/(H t)$ не может быть
  $A$-проективным, а $H$ не может быть $B$-проективным, т.~е. $hd_B (M) > 1$.
]

#theorem(title: [Гильберт])[
  Пусть $A$ — кольцо, $t$ — переменная. Тогда
  $ rtGlDim A[t] = rtGlDim A[t, t^(-1)] = 1 + rtGlDim A. $
] <th:hilbert-syzygy-global-dimension>

#proof[
  Проведём доказательство в три этапа, установив при этом более точный
  результат. Пусть $B_0 = A[t]$ и $B_1 = A[t, t^(-1)]$.
  #condition-list[
    #condition-item(format: "(1°)")[Если $N in moduleCategoryOf(B_i)$, то
      $hd_A (N) <= hd_(B_i) (N)$ $(i = 0, 1)$.]
    <cond:polynomial-dimension-restriction>

    Поскольку $B_i$ — $A$-свободный модуль, то $B_i$-проективная резольвента для
    $N$ является также и $A$-резольвентой.

    #condition-item(format: "(1°)")[Если $M in moduleCategoryOf(A)$, то
      $hd_(B_i) (M tensor_A B_i) = hd_A (M)$ $(i = 0, 1)$.]
    <cond:polynomial-dimension-extension>

    Так как $A$-модуль $M tensor_A B_i$ является прямой суммой экземпляров
    модуля $M$, то из @cond:polynomial-dimension-restriction следует неравенство
    $>=$. Если $P -> M$ есть $A$-проективная резольвента, то
    $P tensor_A B_i -> M tensor_A B_i$ — #source(483)$B_i$-проективная
    резольвента, поскольку функтор $tensor_A B_i$ точный. Это устанавливает
    обратное неравенство.

    #condition-item(format: "(1°)")[Пусть $s = t - 1$. Если
      $M in moduleCategoryOf(B_i)$ ($i = 0$ или $i = 1$), то
      $ hd_(B_i) (M) <= 1 + hd_A (M); $
      <eq:polynomial-dimension-upper-bound>
      при этом равенство имеет место в том случае, когда $M != 0$ и $M s = 0$.
    ] <cond:polynomial-dimension-upper-bound>
  ]

  _Замечание._ Равенство также имеет место, если $M != 0$ и $M s^n = 0$ для
  некоторого $n > 0$.

  Последнее утверждение немедленно следует из
  @prop:kaplansky-central-quotient-dimension, если $hd_A (M) < infinity$, или из
  @eq:polynomial-dimension-upper-bound, если $hd_A (M) = infinity$. Так как
  $B_1 = T^(-1)B_0$, где $T = {t^n | n >= 0}$, то $M = T^(-1)M$ для
  $M in moduleCategoryOf(B_1)$, и поэтому $hd_(B_1) (M) <= hd_(B_0) (M)$,
  поскольку функтор локализации точен. Следовательно, достаточно установить
  @eq:polynomial-dimension-upper-bound для $i = 0$, $B_0 = A[t]$.

  Можно записать: $M = M_f$ ($f$ — умножение на $t$). Тогда получим
  характеристическую последовательность
  @prop:endomorphism-characteristic-sequence:
  $ 0 -> M[t] -> M[t] -> M -> 0. $
  В силу @cond:polynomial-dimension-extension $hd_(B_0) (M[t]) = hd_A (M)$. Из
  @prop:projective-dimension-sequence следует, что
  $hd_(B_0) (M) <= 1 + hd_(B_0) (M[t])$; тем самым
  @cond:polynomial-dimension-upper-bound доказано.

  Очевидно, что теорема следует из @cond:polynomial-dimension-upper-bound,
  поскольку $A = B_i/(s B_i)$ $(i = 0, 1)$.
]

В следующих двух утверждениях $T$ обозначает свободную абелеву группу или
полугруппу с одним образующим $t$, а $T^n$ — произведение $n$ экземпляров группы
$T$. Проводя индукцию по $n$, получаем из
@th:hilbert-syzygy-global-dimension

#corollary[
  $rtGlDim A[T^n] = n + rtGlDim A$.
] <cor:multivariable-global-dimension>

#theorem(title: [Суон])[
  #idx("теорема Суона")Пусть $A$ — нётерово справа кольцо, $S$ — центральная
  мультипликативная система в кольце $A$.
  #condition-list[
    #condition-item(format: "cyrillic")[Если кольцо $A$ регулярно справа, то
      кольцо $A[T^n]$ также регулярно справа.]
    <cond:polynomial-regular-ring>
    #condition-item(format: "cyrillic")[Если система $S$ регулярна относительно
      кольца $A$, то система $S$ регулярна также и относительно кольца
      $A[T^n]$.]
    <cond:polynomial-regular-multiplicative-system>
  ]
] <th:swan-polynomial-regularity>

#proof[
  Часть @cond:polynomial-regular-ring следует из части
  @cond:polynomial-regular-multiplicative-system утверждения в частном случае
  $0 in S$. Часть @cond:polynomial-regular-multiplicative-system следует по
  индукции из случая $n = 1$, с использованием теоремы Гильберта о базисе. Можно
  записать: $A[t, t^(-1)] = U^(-1) A[t]$, где $U = {t^n | n >= 0}$. Таким
  образом, результаты для $A[t, t^(-1)]$ будут следовать из результатов для
  $A[t]$, если учесть следующее замечание: если $S$ и $U$ — центральные
  мультипликативные системы в нётеровом справа кольце $B$ и если система $S$
  регулярна относительно кольца $B$, то система $S$ также регулярна относительно
  кольца $U^(-1)B$. Действительно, пусть $M in bold(M)(U^(-1)B)$. Тогда
  $M = U^(-1)N$, где $N in bold(M)(B)$, #source(484)и можно считать, что
  $N subset M$. Таким образом, если $M s = 0$ для некоторого элемента $s in S$,
  то и $N s = 0$. Считая, что система $S$ регулярна относительно $B$, видим, что
  желаемое неравенство $hd_(U^(-1)B) (M) < infinity$ следует теперь из
  неравенств $hd_B (N) < infinity$ и $hd_(U^(-1)B) (U^(-1)N) <= hd_B (N)$.

  Наконец, мы должны показать, что если $M in bold(M)(A[t])$ и если $M s = 0$
  для некоторого элемента $s in S$, то $hd_(A[t]) (M) < infinity$. В силу части
  @cond:polynomial-dimension-upper-bound доказательства теоремы
  @th:hilbert-syzygy-global-dimension $hd_(A[t]) (M) <= 1 + hd_A (M)$, и поэтому
  достаточно показать, что $hd_A (M) < infinity$. Пусть $M_0 subset M$ — конечно
  порожденный $A$-подмодуль, порождающий $A[t]$-модуль $M$, т.~е.
  $M = sum_(i >= 0) M_0 t^i$. Положим $M_n = M_0 + M_0 t + dots + M_0 t^n$.
  Тогда $M = colim (M_n)$ (как $A$-модуль). Следовательно, достаточно показать,
  что:
  #condition-list[
    #condition-item(format: "(1°)")[размерность $hd_A (M_n)$ ограничена при
      $n -> infinity$;]
    <cond:swan-filtration-bounded-dimension>
    #condition-item(format: "(1°)")[
      $hd_A (colim (M_n)) <= 1 + sup_(n >= 0) hd_A (M_n)$.]
    <cond:swan-sequential-colimit-dimension>
  ]

  @cond:swan-filtration-bounded-dimension Рассмотрим последовательность
  _эпиморфизмов_
  $ M_0 arrow.r^t M_1/M_0 arrow.r^t M_2/M_1 -> dots. $
  Так как $M_0$ — нётеров $A$-модуль, то для некоторого $n_0$ отображение
  $M_n/M_(n-1) arrow.r^t M_(n+1)/M_n$ является изоморфизмом при всех $n >= n_0$.
  Пусть $d = max(hd_A (M_(n_0)), hd_A (M_(n_0)/M_(n_0 - 1)))$. Проведём индукцию
  по $n >= n_0$ и покажем, что $hd_A (M_n) <= d$. Это очевидно для $n = n_0$.
  Если $n > n_0$, то воспользуемся точной последовательностью
  $ 0 -> M_(n-1) -> M_n -> M_n/M_(n-1) -> 0, $
  изоморфизмом $M_n/M_(n-1) tilde.eq M_(n_0)/M_(n_0 - 1)$ и индуктивным
  предположением о том, что $hd_A (M_(n-1)) <= d$; получим, что
  $hd_A (M_n) <= d$. Так как $M_n in bold(M)(A)$ и $M_n s = 0$ при всех $n$, то
  $hd_A (M_n) < infinity$ для любого $n$, поскольку система $S$ регулярна
  относительно $A$. Но в силу сказанного в последнем абзаце
  $
    sup_(0 <= n) hd_A (M_n)
    <= sup(d, hd_A (M_0), dots, hd_A (M_(n_0))) < infinity.
  $

  @cond:swan-sequential-colimit-dimension Рассмотрим точную последовательность
  $
    0 -> union.big.sq_(n >= 0) M_n arrow.r^j union.big.sq_(n >= 0) M_n
    arrow.r^f colim (M_n) -> 0,
  $
  в которой $j(m_0, m_1, m_2, dots) = (m_0, m_1 - m_0, m_2 - m_1, dots)$ и
  $f(m_0, m_1, m_2, dots) = sum m_i$ (аналогичная конструкция может быть
  применена к любым копределам последовательности модулей). Имеем
  $
    hd_A (colim (M_n)) <= 1 + hd_A (union.big.sq_(n >= 0) M_n)
    = 1 + sup_(n >= 0) hd_A (M_n),
  $
  что и требовалось доказать.
]
