#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/polynomial-fundamental-theorem-mayer-vietoris.typ": (
  mayer-vietoris-square, mayer-vietoris-unlabelled-square,
)

== Длинные последовательности Майера — Вьеториса <sec:long-mayer-vietoris>

#source(513)Через $CartCat$ обозначим категорию, объектами которой являются
#symbol-idx($CartCat$, sort: "Cart", group: "categories", order: 4)
декартовы квадраты
#numbered-condition[#mayer-vietoris-square()]
<eq:long-mayer-vietoris-cartesian-square>
в категории колец, такие, что отображение $c'_1$ или $c'_2$ сюръективно. Под
морфизмом в этой категории понимается морфизм диаграмм в обычном смысле.

Если $F: italic("rings") -> moduleCategoryOf(ZZ, side: "left")$ — функтор, то
можно рассмотреть последовательность #numbered-condition[
  $
    F(A) arrow.r^((c_1,c_2)) F(A_1) plus.o F(A_2)
    arrow.r^(c'_1-c'_2) F(A'),
  $
] <eq:mayer-vietoris-functor-sequence>
ассоциированную с функтором $F$ и квадратом $C$. Далее мы всегда будем иметь в
виду именно эту последовательность, даже если отображения и не будут указаны
явно.

#definition[
  #idx("пара Майера — Вьеториса")_Парой Майера — Вьеториса_ будет называться
  тройка $(F_1,F_0,delta)$, где
  $F_1,F_0: italic("rings") -> moduleCategoryOf(ZZ, side: "left")$ — функторы и
  где $delta$ сопоставляет каждому рассмотренному выше квадрату $C in CartCat$
  гомоморфизм
  $ delta_C: F_1 (A') -> F_0 (A), $
  естественный по $C$ и такой, что последовательность
  $
    (M-V)(F_1,F_0;C) =
    (F_1 (A) -> F_1 (A_1) plus.o F_1 (A_2) -> F_1 (A')
      arrow.r^(delta) F_0 (A) -> F_0 (A_1) plus.o F_0 (A_2) -> F_0 (A'))
  $
  точна.
] <def:mayer-vietoris-pair>

#proposition[
  Пусть $((F_1,h_1),(F_0,h_0),delta)$ — пара Майера — Вьеториса стягиваемых
  функторов и $J$ — либо функтор $N$, либо $L$. Тогда
  $ ((J F_1,J h_1),(J F_0,J h_0),J delta) $
  также является парой Майера — Вьеториса стягиваемых функторов ($J delta$ будет
  определено в ходе доказательства).
] <prop:mayer-vietoris-pair-contraction>

#proof[
  #source(514)Пусть $(T,T_±)$ — ориентированный цикл, и пусть $C in CartCat$ —
  рассмотренный выше квадрат. Тогда очевидно, что
  $ C[T_±],C[T] in CartCat. $
  Определим $N delta$ так, чтобы последовательность
  $
    0 -> (M-V)(N F_1,N F_0;C) -> (M-V)(F_1,F_0;C[T_+])
    -> (M-V)(F_1,F_0;C) -> 0
  $
  была (расщепляющейся) точной последовательностью комплексов. В частности,
  левый член этой последовательности — ацикличный комплекс.

  Аналогично определим $L delta$ так, чтобы последовательность
  #numbered-condition[
    $
      (M-V)(F_1,F_0;C[T_+]) plus.o (M-V)(F_1,F_0;C[T_-])
      arrow.r^(tau) (M-V)(F_1,F_0;C[T]) -> (M-V)(L F_1,L F_0;C) -> 0
    $
  ] <eq:mayer-vietoris-contracted-complexes>
  являлась точной последовательностью комплексов. Если заменить левый член этой
  последовательности на $Im (tau)$, то мы получим ацикличный подкомплекс
  среднего члена. Из рассмотрения длинной гомологической последовательности
  получившейся короткой точной последовательности комплексов следует, что правый
  член $(M-V)(L F_1,L F_0;C)$ последовательности ацикличен всюду, кроме,
  возможно, среднего члена последовательности #numbered-condition[
    $ L F_0 (A) -> L F_0 (A_1) plus.o L F_0 (A_2) -> L F_0 (A'). $
  ] <eq:mayer-vietoris-contracted-tail>
  Но $delta$ сюда не входит. Из стягиваемости функтора $F_0$ следует, что точная
  последовательность @eq:mayer-vietoris-contracted-complexes как
  последовательность комплексов расщепляется справа в членах, входящих в
  @eq:mayer-vietoris-contracted-tail. Следовательно, последовательность
  @eq:mayer-vietoris-contracted-tail также является точной. Стягиваемость
  функторов $N F_i$ и $L F_i$ вытекает из
  @prop:contracted-functor-kernels-cokernels, чем и завершается доказательство.
]

#corollary[
  Пусть $(F,h)$ — стягиваемый функтор. Предположим, что существует $delta$, для
  которого $((F,h),(L F,L h),delta)$ — пара Майера — Вьеториса. Тогда для
  диаграммы
  $ C = #mayer-vietoris-unlabelled-square() in CartCat $
  существует «длинная последовательность Майера — Вьеториса»
  $
    F(A) -> dots -> L^(n-1) F(A') -> L^n F(A)
    -> L^n F(A_1) plus.o L^n F(A_2) -> L^n F(A') -> L^(n+1) F(A) -> dots,
  $
  являющаяся точной. Кроме того, $((N^i F,N^i h),(L N^i F,L N^i h,delta))$ также
  является парой Майера — Вьеториса. Поэтому существует #source(
    515,
  )соответствующая длинная последовательность Майера — Вьеториса для функторов
  $(L^n N^i F)$ $(n >= 0)$ при любом $i >= 0$.
] <cor:long-mayer-vietoris-contracted-functor>

#proof[
  Последнее утверждение следует из предложения
  @prop:mayer-vietoris-pair-contraction. Из этого же предложения вытекает, что
  $((L F,L h),(L^2 F,L^2 h),L delta)$ является парой Майера — Вьеториса
  стягиваемых функторов. Аналогичное утверждение имеет место для
  $((L^n F,L^n h),(L^(n+1) F,L^(n+1) h),L^n delta)$ при всех $n >= 0$. Сращивая
  $(M-V)(L^(n-1) F,L^n F,L^(n-1) delta)$ с $(M-V)(L^n F,L^(n+1) F,L^n delta)$
  для каждого $n > 0$, получим длинную последовательность.
]

В силу теоремы Милнора (@th:projective-k-mayer-vietoris) $(K_1,K_0,delta)$ —
пара Майера — Вьеториса. По основной теореме @th:fundamental-k-theory-laurent
можно отождествить функторы $K_0$ и $L K_1$. Поэтому $(K_1,h)$ и $(K_0,L h)$ —
стягиваемые функторы, где $h$ — гомоморфизм из @th:fundamental-k-theory-laurent.
Следовательно, можно применить следствие
@cor:long-mayer-vietoris-contracted-functor, откуда немедленно получается

#theorem[
  Пусть $C$ — диаграмма из @cor:long-mayer-vietoris-contracted-functor. Тогда
  для любого $i >= 0$ существует длинная последовательность Майера — Вьеториса
  $
    F(A) -> dots -> L^(n-1) F(A') -> L^n F(A)
    -> L^n F(A_1) plus.o L^n F(A_2) -> L^n F(A') -> L^(n+1) F(A) -> dots,
  $
  где $F=N^i K_1$. Напомним (@th:fundamental-k-theory-laurent), что
  $ L^n N^i K_1 = N^i L^n K_1, $
  $ N K_1 = NilGroup, $
  $ L K_1 = K_0. $
] <th:long-k-mayer-vietoris>

В случае $i=0$ приведенная в этой теореме последовательность имеет вид
$
  K_1 (A) -> dots -> K_0 (A') -> K_(-1) (A)
  -> K_(-1) (A_1) plus.o K_(-1) (A_2) -> K_(-1) (A') -> K_(-2) (A) -> dots,
$
где
$ K_(-n) (A) = L^n K_0 (A) = L^(n+1) K_1 (A). $
