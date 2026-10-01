#import "main-defs.typ": (
  Aut, End, GL, HCat, Im, K, NilCat, NilGroup, hd, moduleCategoryOf, source,
  symbol-idx,
)
#import "statements.typ": corollary, numbered-condition, proof, proposition

== Категория нильпотентных эндоморфизмов <sec:nilpotent-endomorphisms>

Пусть $bold(C)$ — допустимая подкатегория абелевой категории (в смысле
@def:admissible-abelian-subcategory). Введём теперь категорию
$ NilCat (bold(C)), $
#symbol-idx($NilCat$, sort: "Nil", group: "categories", order: 18)
#source(498)объекты которой — пары $(M,nu)$, где $M in bold(C)$ и эндоморфизм
$nu in End_(bold(C)) (M)$ нильпотентен. Это полная подкатегория категории
эндоморфизмов объектов категории $bold(C)$. Кроме того, у нас есть два точных
функтора:
$
  Z: bold(C) -> NilCat (bold(C)), quad Z(M) = (M,0) quad
  "(«нулевой»)"
$
и
$
  F: NilCat (bold(C)) -> bold(C), quad F(M,nu)=M quad
  #[(«забывающий $nu$»).]
$
Так как $F Z = 1_(bold(C))$, то получаем расщепляющуюся точную
последовательность
$
  0 -> K_0 (bold(C)) arrow.r^Z K_0 (NilCat (bold(C)))
  -> NilGroup (bold(C)) -> 0,
$
определяющую группу $NilGroup (bold(C))$.

#proposition[
  Если $bold(C)$ — абелева категория, то $NilGroup (bold(C)) = 0$.
] <prop:abelian-category-nil-vanishing>

#proof[
  Если $(M,nu) in NilCat (bold(C))$, то рассмотрим фильтрацию
  $M supset nu M supset nu^2 M supset dots$, индуцирующую фильтрацию на $(M,nu)$
  в категории $NilCat (bold(C))$. Имеем
  $ [M,nu] = sum [(nu^i M)/(nu^(i+1) M),0] in Im (Z) $
  в группе $K_0 NilCat (bold(C))$, что и требовалось доказать.
]

#proposition[
  Пусть $bold(C)_0 subset bold(C)$ — допустимые подкатегории абелевой категории.
  Допустим, что каждый объект $M$ категории $bold(C)$ является факторобъектом
  некоторого объекта категории $bold(C)_0$ и что, если последовательность
  $0 -> P_n -> dots -> P_0 -> M -> 0$ точна для некоторого $n=n(M)$, причём
  $P_i in bold(C)_0$ $(0 <= i < n)$, то $P_n in bold(C)_0$. Тогда это же
  утверждение верно и для категорий
  $NilCat (bold(C)_0) subset NilCat (bold(C))$. Следовательно, отображение
  $ K_0 (NilCat (bold(C)_0)) -> K_0 (NilCat (bold(C))) $
  является изоморфизмом.
] <prop:nilpotent-category-resolution>

#proof[
  Последнее утверждение вытекает из @th:grothendieck-resolution-k0. Первое
  утверждение докажем для $(M,nu) in NilCat (bold(C))$, проведя индукцию по
  $n=n(M)$. Допустим, что $n>0$ (случай $n=0$ тривиален). Выберем точную
  последовательность $0 -> N -> P arrow.r^f M -> 0$, где $P in bold(C)_0$.

  Пусть $nu^(h+1)=0$ и $Q=P_0 plus.o P_1 plus.o dots plus.o P_h$, где $P_i=P$.
  Определим $mu in End_(bold(C)) (Q)$, полагая $mu|P_(i-1)$ равным
  тождественному морфизму из $P_(i-1)$ в $P_i$ $(1 <= i <= h)$ и $mu(P_h)=0$.
  Тогда $mu^(h+1)=0$. Поэтому $(Q,mu) in NilCat (bold(C)_0)$. Определим
  $g:Q -> M$, полагая $g|P_i = nu^i f$. Так как $P_i=mu^i P_0$, то $g mu=nu g$.
  Следовательно, получаем точную #source(499)последовательность
  $ 0 -> (H,mu|H) -> (Q,mu) arrow.r^g (M,nu) -> 0 $
  в категории $NilCat (bold(C))$, где $Q in bold(C)_0$. Так как $f$ — эпиморфизм
  и $g|P_0=f$, то $g$ — эпиморфизм. Очевидно, что $n(H) <= n(M)-1$, и поэтому
  можно применить индукцию, чем и завершается доказательство.
]

Для кольца $A$ введём обозначение
$ NilGroup (A) = NilGroup (bold(P)(A)). $

#corollary[
  Для всякого кольца $A$
  $ NilGroup (A) = NilGroup (HCat (A)), $
  причём если $A$ регулярно справа, то $NilGroup (A)=0$.
] <cor:regular-ring-nil-vanishing>

#proof[
  Первое утверждение следует из @prop:nilpotent-category-resolution, так как в
  силу определения объекты категории $HCat (A)$ обладают конечными
  $bold(P)(A)$-резольвентами. Если кольцо $A$ регулярно справа, то категория
  $HCat (A)=bold(M)(A)$ абелева и потому (см.
  @prop:abelian-category-nil-vanishing) $NilGroup (HCat (A))=0$, что и
  требовалось доказать.
]

#proposition[
  Пусть $T_+$ — свободная полугруппа с одним образующим $t$ и $A$ — кольцо.
  Тогда естественный изоморфизм категории $moduleCategoryOf(A[t])$ и категории
  эндоморфизмов правых $A$-модулей (см.
  §~@sec:endomorphism-characteristic-sequence) индуцирует изоморфизмы
  $ bold(M)_(T_+) (A[t]) -> NilCat (bold(M)(A)) $
  и
  $ HCat_(T_+) (A[t]) -> NilCat (HCat (A)). $
  Следовательно,
  $ K_0 (HCat_(T_+) (A[t])) = K_0 (A) plus.o NilGroup (A). $
] <prop:nilpotent-endomorphism-torsion-categories>

Замечание. Позже мы рассмотрим также полугруппу $T_-$, порождённую элементом
$t^(-1)$ (отсюда и обозначение).

#proof[
  Напомним, что $bold(M)_(T_+) (A[t])$ — это категория модулей
  $M in bold(M)(A[t])$, для которых $T_+^(-1) M=0$, или, что эквивалентно,
  $M t^n=0$ при некотором $n>=0$. Единственное, что требует доказательства в
  первом утверждении, — это конечнопорождённость $A$-модуля $M$. Заметим, что
  каждый из модулей $(M t^(i-1))/(M t^i)$ $(i>=1)$ конечно порождён над кольцом
  $A[t]$ и, следовательно, над кольцом $A$. Но эти модули являются
  последовательными факторами в конечной фильтрации на модуле $M$. Поэтому
  $M in bold(M)(A)$, что и требовалось доказать.

  Если $M in HCat_(T_+) (A[t])$, то, поскольку $hd_A (M) <= hd_(A[t]) (M)$ (см.
  часть @cond:polynomial-dimension-restriction доказательства теоремы
  @th:hilbert-syzygy-global-dimension), $M in HCat (A)$. Обратно, #source(
    500,
  )если $M in moduleCategoryOf(A[t])$ и $hd_A (M) < infinity$, то
  $hd_(A[t]) (M) < infinity$, поскольку $hd_(A[t]) (M) <= hd_A (M)+1$ (часть
  @cond:polynomial-dimension-upper-bound доказательства теоремы
  @th:hilbert-syzygy-global-dimension). Тем самым получен второй из приведённых
  выше изоморфизмов категорий.

  Используя это и @prop:nilpotent-category-resolution, видим, что
  $
    K_0 (HCat_(T_+) (A[t])) = K_0 (NilCat (HCat (A)))
    = K_0 (NilCat (bold(P)(A)))
    = K_0 (bold(P)(A)) plus.o NilGroup (bold(P)(A))
    = K_0 (A) plus.o NilGroup (A),
  $
  чем и завершается доказательство.
]

Если $(P,nu) in NilCat (bold(P)(A))$, то рассмотрим
$partial_1 (nu) = 1_P-nu in Aut_A (P)$. Аналогично,
$(P[t],t nu) in NilCat (bold(P)(A[t]))$ и $partial_1 (t nu) = 1_(P[t])-t nu$.
Существует каноническое вложение кольца $End (P)$ в кольцо $End_(A[t]) (P[t])$.
Поэтому определим #numbered-condition[
  $
    partial_+: NilCat (bold(P)(A)) -> Sigma bold(P)(A[t]), quad
    (P,nu) mapsto (P[t],partial_+ (nu)),
  $
] <eq:nilpotent-polynomial-character-functor>
где $partial_+ (nu) = partial_1 (nu)^(-1) partial_1 (t nu)$. Очевидно, что
заданное таким образом на объектах отображение определяет точный функтор. Кроме
того, пополнение $t mapsto 1$ из $A[t]$ в $A$ переводит $partial_+ (nu)$ в
$1_P$. Если $nu=0$, то $partial_+ (nu)=1_(P[t])$. Следовательно, функтор
@eq:nilpotent-polynomial-character-functor индуцирует гомоморфизм
#numbered-condition[
  $
    partial_+: NilGroup (A) -> K_1 (A[t],(t-1)A[t]), quad
    partial_+ [P,nu] = [P[t],partial_+ (nu)],
  $
] <eq:nilpotent-polynomial-character-map>
#symbol-idx($partial_+$, sort: "∂_+", group: "letters", order: 78)
где
$
  partial_+ (nu) = partial_1 (nu)^(-1) partial_1 (t nu)
  quad "и" quad partial_1 (nu)=I-nu.
$
В следующем параграфе мы увидим, что отображение
@eq:nilpotent-polynomial-character-map является изоморфизмом. Сейчас мы лишь
покажем, что имеет место

#proposition[
  Приведённый выше гомоморфизм @eq:nilpotent-polynomial-character-map является
  сюръективным отображением.
] <prop:nilpotent-polynomial-character-surjection>

#proof[
  Положим $s=t-1$. Из @cor:graded-relative-k-one-unipotents следует, что каждый
  элемент группы $K_1 (A[t],s A[t])$ обладает представителем вида
  $I-s nu_1 in GL_n (A[t],s A[t])$ (для некоторого $n$), где $nu_1$ —
  нильпотентная матрица над кольцом $A$, которую мы можем отождествить с
  эндоморфизмом модуля $A^n$. Пусть $nu$ — любой нильпотентный эндоморфизм
  модуля $A^n$. Мы хотим подобрать $nu$ так, чтобы $partial_+ (nu)=I-s nu_1$.
  Напомним, что
  $
    partial_+ (nu)=partial_1 (nu)^(-1)(I-t nu)
    =partial_1 (nu)^(-1)(I-nu-(t-1)nu)
    =I-s partial_1 (nu)^(-1)nu.
  $
  #source(501)Мы закончим доказательство, показав, что
  $nu_1=partial_1 (nu)^(-1)nu$, где $nu=I-(I+nu_1)^(-1)$. Последнее равенство
  влечёт за собой равенство $partial_1 (nu)=(I+nu_1)^(-1)$, т.~е.
  $I+nu_1=partial_1 (nu)^(-1)$, или $nu_1=partial_1 (nu)^(-1)-I$. Но
  $partial_1 (nu)^(-1)=sum_(i>=0) nu^i$. Поэтому
  $
    partial_1 (nu)^(-1)-I=sum_(i>0) nu^i
    =nu sum_(i>=0) nu^i=nu partial_1 (nu)^(-1),
  $
  что и требовалось доказать.
]
