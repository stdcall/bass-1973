#import "main-defs.typ": (
  Aff, Aut, Center, E, End, GL, Hom, Im, U, idx, moduleCategory, semidirect,
  source, symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, item-record, proof, proposition,
)
#import "diagrams/stable-projective-diagrams.typ": map-arrow

== Аффинная группа модуля <sec:affine-module-group>

Сейчас удобно сделать ряд простых замечаний о группах элементарных
автоморфизмов, введенных в §~@sec:cancellation-elementary-automorphisms. Эти
результаты будут использованы в следующей главе. Зафиксируем кольцо $A$.

#proposition[
  Пусть $P_1, dots, P_n in bold(P)(A)$. Допустим, что по крайней мере два из
  модулей $P_i$ строго проективны. Пусть $P = P_1 plus.o dots plus.o P_n$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[аддитивная группа, порожденная группой
      $E(P_1, dots, P_n)$, совпадает с
      $End_A (P)$;] <cond:elementary-additive-endomorphisms>

    #condition-item(format: "cyrillic")[централизатор в $Aut_A (P)$ подгруппы
      $E(P_1, dots, P_n)$ совпадает с центром группы $Aut_A (P)$, который равен
      ${c 1_P | c in U(Center(A))}$;] <cond:elementary-centralizer>

    #condition-item(format: "cyrillic")[аддитивная подгруппа модуля $P$,
      инвариантная относительно $E(P_1, dots, P_n)$, имеет вид $P frak(a)$, где
      $frak(a) subset A$ — однозначно определенный левый идеал; при этом
      подгруппа $P frak(a)$ также инвариантна относительно
      $End_A (P)$.] <cond:elementary-invariant-subgroups>
  ]
] <prop:elementary-endomorphism-generation>

#proof[
  Пусть $B = End_A (P)$ и $B_0$ — аддитивная группа, порожденная
  $E = E(P_1, dots, P_n)$. Тогда централизаторы групп $E$ и $B_0$ в $B$
  совпадают, а подгруппа модуля $P$, инвариантная относительно $E$, является
  $B_0$-модулем. Следовательно, из @cond:elementary-additive-endomorphisms
  вытекают @cond:elementary-centralizer и @cond:elementary-invariant-subgroups.
  Действительно, так как модуль $P$ строго проективен, то из
  @th:morita-equivalence-properties и @prop:equivalence-from-strict-projective
  следует, что $Center(B) = Center(A)$ и что каждый $B$-подмодуль в $P$ имеет
  вид, указанный в @cond:elementary-invariant-subgroups.

  Остается доказать @cond:elementary-additive-endomorphisms. Из определения
  группы $E(P_1, dots, P_n)$ ясно, что аддитивная группа $B_0$, ею порожденная,
  порождается $I (= 1_P)$ и всеми $Hom_A (P_i, P_j)$ ($i != j$). Следовательно,
  нам надо лишь показать, как получить $Hom_A (P_i, P_i)$ для каждого $i$.
  Предположим, что нам дан эндоморфизм $f = g h$ модуля $P_i$, разлагающийся в
  произведение $P_i #map-arrow($h$) P_j #map-arrow($g$) P_i$ для некоторого
  $j != i$. Тогда
  $
    (I + g)(I + h) = I + g + h + g h in E(P_1, dots, P_n)
  $
  и $I, g, h in B_0$. Из наших предположений следует, что мы можем выбрать
  $j != i$ так, чтобы модуль $P_j$ был строго проективен. Следовательно,
  достаточно показать, что $End_A (P_i)$ аддитивно порождается эндоморфизмами,
  «пропускающимися» через модуль $P_j$. Если $f in End_A (P_i)$ пропускается
  через $P_j^n$, то $f$ является суммой $n$ эндоморфизмов, пропускающихся через
  $P_j$. Для достаточно боль#source(157)ших $n$ модуль $P_j^n$ содержит прямое
  слагаемое, изоморфное модулю $A$. Так как $P_i in bold(P)(A)$, то из
  @prop:equivalence-from-strict-projective
  @cond:strict-projective-finite-generation следует, что кольцо $End_A (P_i)$
  аддитивно порождается эндоморфизмами, пропускающимися через $A$, а
  следовательно, и через $P_j^n$. Предложение доказано.
]

Прежде чем вводить понятие аффинной группы, приведем некоторые обозначения из
теории групп.

Пусть $G$ — группа и $x, y, z in G$. Тогда будем писать $x^y = y^(-1) x y$ и
$[x, y] = x^(-1) y^(-1) x y = x^(-1) x^y$. Известны следующие формулы, которые
можно легко проверить:

#item-record[$
  (x^y)^z = x^(y z) = (x^z)^(y^z), \
  [x, y]^(-1) = [y, x], \
  [x, y z] = [x, z] [x, y]^z, \
  [x y, z] = [x, z]^y [y, z].
$] <ss:group-commutator-identities>

Если $H$ и $H'$ — подгруппы группы $G$, то через $[H, H']$ обозначим подгруппу,
порожденную всеми элементами вида $[x, x']$ ($x in H$, $x' in H'$).

Пусть $P$ — группа, на которой группа $G$ действует как группа автоморфизмов
($x arrow.r.bar alpha(x)$, $x in P$, $alpha in G$). (Задание этой структуры
эквивалентно заданию гомоморфизма $G -> Aut(P)$.) Тогда можно образовать
_полупрямое произведение_,#idx("полупрямое произведение")
$
  P semidirect G,
$
которое определяется как множество $P times G$ с операцией умножения
$
  (x, alpha)(y, beta) = (x dot alpha(y), alpha beta).
$
Например, $(x, alpha)^(-1) = (alpha^(-1)(x^(-1)), alpha^(-1))$. Можно
отождествить $x in P$ с $(x, 1)$ и $alpha in G$ с $(1, alpha)$. В этом случае
$P$ является нормальным делителем группы $P semidirect G$, и мы получаем
расщепляющееся расширение групп:
$
  1 -> P -> P semidirect G -> G -> 1.
$
Предположим, что $P$ — аддитивная абелева группа. Тогда удобно использовать
матричные обозначения и писать
$
  mat(1, 0; x, alpha) quad "вместо" (x, alpha).
$
В этой записи групповой закон превращается в равенство
$
  mat(1, 0; x, alpha) mat(1, 0; y, beta)
  = mat(1, 0; x + alpha(y), alpha beta),
$
#source(158)т.~е. в правило умножения матриц. Легко проверить следующие формулы,
где $I$ обозначает единицу группы $G$:
$
  mat(1, 0; x, alpha)^(-1) = mat(1, 0; -alpha^(-1)(x), alpha^(-1)), \
  mat(1, 0; y, I)^(mat(1, 0; x, alpha)) = mat(1, 0; alpha^(-1)(y), I).
$ <eq:affine-matrix-identities>

Наконец, если $P in moduleCategory hyph A$, то введем в рассмотрение _аффинную
группу модуля_:#idx("аффинная группа модуля")
$
  Aff_A (P) = P semidirect Aut_A (P)
  = "“"mat(1, 0; P, Aut_A (P))"”".
$
#symbol-idx($Aff$, sort: "Aff", group: "operators", order: 29)
В случае когда $P = A^n$, будем обозначать эту группу через
$
  Aff_n (A) = {mat(1, 0; x, alpha) | x in A^n, alpha in GL_n (A)}.
$
Она является подгруппой группы $GL_(n + 1) (A)$.

#proposition[
  Пусть $P in moduleCategory hyph A$, $H$ — подгруппа группы $Aff_A (P)$ и $L$ —
  ее проекция в группу $Aut_A (P)$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[
      $[H, P] = [L, P] = sum_(alpha in L) Im(alpha - 1_P)$;]
    <cond:affine-commutator-image>

    #condition-item(format: "cyrillic")[если подгруппа $H$ нормализуется группой
      $P$, то $[H inter P = {1}] ==> [H = {1}]$;]
    <cond:affine-disjoint-normalized-subgroup>

    #condition-item(format: "cyrillic")[если $P = P_1 plus.o dots plus.o P_n$ —
      такое же разложение, как в @prop:elementary-endomorphism-generation, и
      если подгруппа $H$ нормализуется группой $E(P_1, dots, P_n)$, то
      существуют однозначно определенные левые идеалы $frak(a), frak(b)$ кольца
      $A$, такие, что $H inter P = P frak(a)$ и $[H, P] = P frak(b)$. Если
      $L != {1}$, то $frak(b) != 0$.] <cond:affine-invariant-ideals>
  ]
] <prop:affine-subgroup-commutators>

#proof[
  @cond:affine-commutator-image Это утверждение следует немедленно из последней
  формулы @eq:affine-matrix-identities.

  @cond:affine-disjoint-normalized-subgroup Если $P$ нормализует подгруппу $H$,
  то $[H, P] subset H inter P$. Следовательно, если $H inter P = {1}$, то из
  формул @eq:affine-matrix-identities ясно, что $H subset P$, чем и доказано
  @cond:affine-disjoint-normalized-subgroup.

  @cond:affine-invariant-ideals Если $E(P_1, dots, P_n)$ нормализует подгруппу
  $H$, то $H inter P$ и $[H, P]$ являются аддитивными подгруппами группы $P$,
  инвариантными относительно $E(P_1, dots, P_n)$. Следовательно,
  @cond:affine-invariant-ideals вытекает из
  @prop:elementary-endomorphism-generation @cond:elementary-invariant-subgroups
  и из утверждения @cond:affine-commutator-image.
]
