#import "main-defs.typ": (
  End, Hom, Im, ann, det, moduleCategory, name-idx, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, example, item-record, lemma, proof,
  proposition,
)
#import "diagrams/module-categories-diagrams.typ": (
  generated-equivalence, projective-dual-basis,
)

== Построение эквивалентности, исходя из модуля <sec:equivalence-from-module>

До сих пор в нашем изложении подчеркивалась симметрия, присущая ситуации
эквивалентности. С другой стороны, из теоремы @th:morita-equivalence-properties
следует, что некоторая часть ситуации эквивалентности уже определяет ее
полностью.

Начнем с $R$-алгебры $B$ и правого $B$-модуля $P$. Исходя из этого, создадим
ситуацию предэквивалентности, а затем найдем условия на модуль $P$, при которых
возникает ситуация эквивалентности.

Положим
$
  A = End_B (P) quad "и" quad Q = Hom_B (P, B).
$
Тогда $A$ есть $R$-алгебра и $P$~— левый $A tensor_R B^degree$-модуль. Кроме
того, $Q$~— левый $B tensor_R A^degree$-модуль относительно действия
$
  (b q) p = b(q p) quad (b in B, q in Q, p in P)
$
и
$
  (q a) p = q(a p) quad (q in Q, a in A, p in P).
$
Определим теперь гомоморфизмы бимодулей
$
  f_P: P tensor_B Q -> A quad "и" quad g_P: Q tensor_A P -> B.
$
Отображение $g_P$ является «значением»: $g_P (q tensor p) = q p$. Определим
$f_P (p tensor q) = p q in A = End_B (P)$, полагая
$
  (p q) p' = p(q p') quad (p' in P).
$
Из леммы @lem:morita-context-associativity следует

#proposition[
  Пусть $B$ есть $R$-алгебра, $P$~— правый $B$-модуль и $f_P$, $g_P$~—
  определенные выше гомоморфизмы. Тогда

  #item-record[
    $(A = End_B (P), B, P, Q = Hom_B (P, B), f_P, g_P)$~— ситуация
    предэквивалентности (см. определение @def:morita-context).
  ] <ss:module-canonical-morita-context>
] <prop:module-canonical-morita-context>

#example[
  Пусть $P = e B$, где $e$~— идемпотент. Тогда $B = P plus.o (1 - e) B$, поэтому
  $q: P -> B$ можно продолжить до $overline(q): B -> B$, полагая
  $overline(q)((1 - e) B) = 0$. Таким образом, получаем #source(69)включения
  $
    A = Hom_B (P, P) subset Q = Hom_B (P, B) subset B = Hom_B (B, B).
  $
  При этих отождествлениях мы видим, что
  $
    P = e B, quad Q = B e quad "и" quad A = e B e,
  $
  и все спаривания индуцированы умножением в $B$. В частности, отображение
  $f_P: e B tensor_B B e -> A = e B e$ сюръективно, а образ отображения
  $g_P: B e tensor_(e B e) e B -> B$ совпадает с двусторонним идеалом $B e B$,
  порожденным элементом $e$.
] <exm:idempotent-morita-context>

#proposition[
  В обозначениях предложения @prop:module-canonical-morita-context

  #condition-list[
    #condition-item(format: "cyrillic")[[отображение $f_P$ сюръективно] $<=>$
      [$P$~— конечно порожденный проективный $B$-модуль], и в этом случае
      $f_P$~— изоморфизм;] <cond:strict-projective-finite-generation>

    #condition-item(format: "cyrillic")[[отображение $g_P$ сюръективно] $<=>$
      [$P$~— образующий категории $moduleCategory hyph B$], и в этом случае
      $g_P$~— изоморфизм;] <cond:strict-projective-generator>

    #condition-item(format: "cyrillic")[[@ss:module-canonical-morita-context
      является ситуацией эквивалентности] $<=>$ [$P$~— строго проективный
      $B$-модуль], и в этом случае функторы
      $ #generated-equivalence() $
      осуществляют эквивалентность.] <cond:strict-projective-equivalence>
  ]
] <prop:equivalence-from-strict-projective>

#proof[
  Импликации $=>$ в @cond:strict-projective-finite-generation и
  @cond:strict-projective-generator следуют из предложения
  @prop:module-canonical-morita-context и теоремы @th:surjective-morita-context.
  Пункт @cond:strict-projective-equivalence следует из
  @cond:strict-projective-finite-generation и @cond:strict-projective-generator
  (см. предложение @prop:strict-projective-modules) и из теоремы
  @th:morita-equivalence-properties, если учесть тот факт, что функторы
  $Hom_B (P, dot)$ и $tensor_B Hom_B (P, B)$ изоморфны, если модуль $P$ конечно
  порожден и проективен (см. доказательство утверждения
  @th:morita-equivalence-properties @cond:morita-left-module-equivalence). Если
  $P$~— образующий, то существует эпиморфизм $(q_i)_(i in I): P^((I)) -> B$ и
  потому $Im g_P supset sum q_i P = B$, следовательно, отображение $g_P$
  сюръективно.

  Другая импликация в п. @cond:strict-projective-finite-generation немедленно
  следует из более общего утверждения:
]

#proposition[
  [Правый $B$-модуль $P$ проективен] $<=>$ [существуют множества $(p_i)$,
  $p_i in P$ и $(q_i)$, $q_i in Q = Hom_B (P, B)$ $(i in I)$, такие, что для
  любого $p in P$

  #condition-list[
    #condition-item[$q_i p = 0$ почти для всех
      $i$;] <cond:dual-basis-finite-support>

    #condition-item[$sum p_i (q_i p) = p$.] <cond:dual-basis-reconstruction>
  ]]

  Возникающие при этом множества $(p_i)$ являются в точности системами
  образующих модуля $P$. Кроме того, идеал $frak(a) = Im g_P = sum q P$
  $(q in Q)$ порожден как двусторонний идеал элементами множества ${q_j p_i}$,
  $P frak(a) = P$ и $frak(a)^2 = frak(a)$.
] <prop:projective-dual-basis>

#proof[
  #source(70)Проективность модуля $P$ равносильна существованию гомоморфизмов
  $ #projective-dual-basis() $
  таких, что $h e = 1_P$. Первое утверждение является переформулировкой этого
  уравнения. Если модуль $P$ проективен, то возникающие при этом отображения $h$
  являются эпиморфизмами. Отсюда следует второе утверждение.

  Для доказательства третьего утверждения пусть $p in P$ и $q in Q$. Тогда
  $
    q p = q sum_i p_i (q_i p)
    = sum_(i, j) q(p_j (q_j p_i)(q_i p))
    = sum_(i, j)(q p_j)(q_j p_i)(q_i p).
  $
  Из @cond:dual-basis-reconstruction следует, что $P frak(a) = P$, поэтому
  $frak(a) = Q P = Q P Q P = frak(a)^2$.
]

Закончим этот параграф описанием строго проективных модулей над коммутативными
кольцами.

#lemma[
  Пусть $P$~— конечно порожденный модуль над коммутативным кольцом $B$, и пусть
  $frak(a)$~— такой $B$-идеал, что $P frak(a) = P$. Тогда $P(1 - a) = 0$ для
  некоторого элемента $a in frak(a)$.
] <lem:finite-module-idempotent-ideal>

#proof[
  Если элементы $x_1, dots, x_n$ порождают модуль $P$, то в силу условия леммы
  $x_i = sum_j x_j a_(j i)$ для любого $i$ и для подходящих
  $a_(j i) in frak(a)$. Из равенства $sum_j x_j (delta_(j i) - a_(j i)) = 0$
  $(1 <= i <= n)$ следует, что $x_j d = 0$ $(1 <= j <= n)$ (в силу правила
  Крамера), где $d = det(delta_(j i) - a_(j i)) equiv 1 mod frak(a)$.
]

#proposition[
  Пусть $B$~— коммутативное кольцо, $P$~— проективный $B$-модуль и
  $frak(a) = Im g_P = sum q P$ $(q in Q = Hom_B (P, B))$. Если идеал $frak(a)$
  конечно порожден (например, если кольцо $B$ нётерово или если модуль $P$
  конечно порожден), то $frak(a) = e B$, где $e^2 = e$ и
  $ann_B (P) = (1 - e) B$. Следовательно, $P$ является образующим в категории
  $moduleCategory hyph B$ тогда и только тогда, когда модуль $P$ точный (т. е.
  $ann_B (P) = 0$).
] <prop:commutative-projective-trace-ideal>

#proof[
  В предложении @prop:projective-dual-basis показано, что $frak(a)^2 = frak(a)$.
  В наших предположениях применима лемма @lem:finite-module-idempotent-ideal (с
  $P = frak(a)$), поэтому $frak(a)(1 - e) = 0$ для некоторого $e in frak(a)$.
  Ясно, что $e^2 = e$ и $frak(a) = e frak(a) = e B$. Кроме того, опять в силу
  предложения @prop:projective-dual-basis $P frak(a) = P$, и потому
  $P(1 - e) = 0$. Пусть $e = sum q_i p_i$. Тогда, если $a in ann_B (P)$, то
  $e a = sum(q_i p_i) a = sum q_i (p_i a) = 0$ и, следовательно,
  $a = (1 - e) a in (1 - e) B$. Таким образом, $ann_B (P) = (1 - e) B$. Наконец,
  $P$ является образующим $<=> frak(a) = B <=> e = 1
  <=> ann_B (P) (= (1 - e) B) = 0$.
]

#corollary[
  Модуль над коммутативным кольцом строго проективен (в смысле
  §~@sec:module-category-characterization) тогда и только тогда, когда он
  конечно порожден, проективен и точен.
] <cor:commutative-strict-projective-modules>

#source(71)*Примеры.* 1 (см. пример @exm:idempotent-morita-context). Пусть $B$~—
кольцо матриц вида $mat(a, b; 0, c)$ над полем $k$, и пусть
$e = mat(1, 0; 0, 0)$. Тогда $P = e B$ является конечно порожденным проективным
и точным правым $B$-модулем. Однако $Im g_P = P != B$, и поэтому $P$ не является
образующим в $moduleCategory hyph B$, т. е. модуль $P$ не является строго
проективным. Конечно, кольцо $B$ некоммутативно.

2 (Капланский).#name-idx("Капланский (Kaplansky I.)") Пусть $B$~—
(коммутативное) кольцо непрерывных действительнозначных функций на отрезке
$[0, 1]$, $P$~— идеал всех функций, обращающихся в нуль на некоторой (зависящей
от функции) окрестности нуля. Известно, что $P$~— проективный модуль. (Надо лишь
построить $p_i$ и $q_i$, как в предложении @prop:projective-dual-basis,
используя умножение на подходящие «ступенчатые» функции в качестве $q_i$.) Кроме
того, легко заметить, что $P$~— точный модуль. Если $frak(a) = Im g_P$, то
$P subset frak(a)$ (благодаря вложению $P subset B$, являющемуся линейным
функционалом $P arrow.r.hook B$). Нетрудно показать даже, что $P = frak(a)$.
Таким образом, $P$ не является образующим в категории $moduleCategory hyph B$,
и, следовательно, модуль $P$ не является строго проективным. Конечно, модуль $P$
не является конечно порожденным.
