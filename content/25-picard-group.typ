#import "main-defs.typ": (
  Aut, End, Hom, Im, InAut, Int, Ker, Pic, PicCat, alg, idx, moduleCategory,
  source, symbol-idx, tensor,
)
#import "statements.typ": condition-item, condition-list, proof, proposition
#import "diagrams/module-categories-diagrams.typ": map-arrow, picard-equivalence

== Классы автоэквивалентностей: группа Пикара <sec:picard-group>

Пусть $R$~— коммутативное кольцо. Если $bold(A)$ есть $R$-категория, то
определим
$
  Pic_R (bold(A))
$
#idx("группа Пикара")#symbol-idx(
  $Pic$,
  sort: "Pic",
  group: "operators",
  order: 66,
)как группу классов $[T]$ изоморфных $R$-эквивалентностей
$T: bold(A) -> bold(A)$. Групповая операция индуцируется композицией функторов.

Если $A$~— некоторая $R$-алгебра, то определим
$
  Pic_R (A)
$
как группу классов $[P]$ изоморфных обратимых левых
$A tensor_R A^degree$-модулей. Групповая операция $[P][Q] = [P tensor_A Q]$. Из
@cor:invertible-bimodule и утверждения @cond:morita-duals теоремы
@th:morita-equivalence-properties следует, что это действительно группа, в
которой
$
  [P]^(-1) = [Hom_(moduleCategory hyph A)(P, A)]
  = [Hom_(A hyph moduleCategory)(P, A)].
$
Согласно теореме @th:eilenberg-watts, имеет место

#proposition[
  Существуют взаимно обратные антиизоморфизмы
  $ #picard-equivalence(), $
  где $alpha[P] = [tensor_A P]$ и $beta[T] = [T A]$.
] <prop:picard-category-isomorphism>

#source(72)Интуитивно ясно, что автоморфизмы алгебры $A$ должны влиять на группу
$Pic_R (moduleCategory hyph A)$. Покажем, как они появляются в $Pic_R (A)$.

Если $A$ есть $R$-алгебра, то через $PicCat_R (A)$ #symbol-idx(
  $PicCat$,
  sort: "Pic",
  group: "categories",
  order: 20,
)обозначим категорию обратимых левых $A tensor_R A^degree$-модулей с
гомоморфизмами бимодулей в качестве морфизмов. Пусть $P in PicCat_R (A)$ и
$alpha, beta in Aut_(R hyph alg)(A)$, #symbol-idx(
  $hyph alg$,
  sort: "-alg",
  group: "categories",
  order: 0,
)обозначим тогда через
$
  attach(P, bl: alpha, br: beta)
$
левый $A tensor_R A^degree$-модуль, аддитивная группа которого совпадает с $P$,
а структура бимодуля задается следующим образом:
$
  a dot p = alpha(a) p, quad p dot a = p beta(a)
  quad (p in P, a in A).
$
Таким образом, например, $P = attach(P, bl: 1, br: 1)$. Кроме того, очевидно,
что
$
  attach(P, bl: alpha, br: beta) tilde.eq attach(A, bl: alpha, br: 1)
  tensor_A P tensor_A attach(A, bl: 1, br: beta).
$
Предположим, что $P, Q in PicCat_R (A)$ и что $f: P -> Q$ является левым
$A$-изоморфизмом. Так как $A = Hom_(A hyph moduleCategory)(P, P)^degree$, то
левый $A$-эндоморфизм $p arrow.r.bar f^(-1)(f(p) a)$ должен задаваться
умножением справа на однозначно определенный элемент $alpha(a) in A$. Другими
словами,
$
  f(p alpha(a)) = f(p) a quad (p in P, a in A).
$
Очевидно, $alpha in Aut_(R hyph alg)(A)$, и это равенство означает, что
$f: attach(P, bl: 1, br: alpha) -> Q$ является изоморфизмом бимодулей. Это
доказывает утверждение @cond:twisted-bimodule-free-left-module из следующего
предложения:

#proposition[
  Пусть $A$~— произвольная $R$-алгебра, и пусть
  $alpha, beta, gamma in Aut_(R hyph alg)(A)$. Тогда

  #condition-list[
    #condition-item[$attach(A, bl: alpha, br: beta)
      tilde.eq attach(A, bl: gamma alpha, br: gamma beta)$ как
      бимодули;] <cond:twisted-bimodule-common-automorphism>

    #condition-item[$attach(A, bl: 1, br: alpha) tensor_A
      attach(A, bl: 1, br: beta)
      tilde.eq attach(A, bl: 1, br: alpha beta)$ как
      бимодули;] <cond:twisted-bimodule-tensor-product>

    #condition-item[[$attach(A, bl: 1, br: alpha)
      tilde.eq attach(A, bl: 1, br: 1)$ как бимодули] $<=>$ [$alpha$ принадлежит
      $InAut(A)$, т. е. группе внутренних автоморфизмов];#symbol-idx(
        $InAut$,
        sort: "In Aut.",
        group: "operators",
        order: 56,
      )] <cond:twisted-bimodule-inner>

    #condition-item[если $P in PicCat_R (A)$ и если $P tilde.eq A$ как левые
      $A$-модули, то $P tilde.eq attach(A, bl: 1, br: alpha)$ как бимодули для
      некоторого
      $alpha in Aut_(R hyph alg)(A)$.] <cond:twisted-bimodule-free-left-module>
  ]
] <prop:picard-twisted-bimodules>

#proof[
  @cond:twisted-bimodule-common-automorphism Отображение
  $x arrow.r.bar gamma(x)$ является требуемым изоморфизмом.

  @cond:twisted-bimodule-tensor-product Используя
  @cond:twisted-bimodule-common-automorphism, получаем, что
  $
    attach(A, bl: 1, br: alpha) tensor_A attach(A, bl: 1, br: beta)
    tilde.eq attach(A, bl: alpha^(-1), br: 1)
    tensor_A attach(A, bl: 1, br: beta)
    tilde.eq attach(A, bl: alpha^(-1), br: beta)
    tilde.eq attach(A, bl: 1, br: alpha beta).
  $

  @cond:twisted-bimodule-inner Если
  $f: attach(A, bl: 1, br: alpha) -> attach(A, bl: 1, br: 1)$~— изоморфизм
  бимодулей, то (как левый $A$-автоморфизм) $f(x) = x u$, где $u = f(1)$
  является обратимым элементом в кольце $A$. Кроме того,
  $f(alpha(a)) = f(1 dot a) = f(1) a$, откуда $alpha(a) u = u a$, т. е.
  $alpha(a) = u a u^(-1)$ для всех $a in A$.

  Обратно, если $alpha(a) = u a u^(-1)$ для некоторого обратимого элемента
  $u in A$, то $f(x) = x u$ является изоморфизмом бимодулей
  $attach(A, bl: 1, br: alpha) -> attach(A, bl: 1, br: 1)$.

  @cond:twisted-bimodule-free-left-module Было доказано выше.
]

#source(73)Группа $Pic_R (A hyph moduleCategory) tilde.eq Pic_R (A)$ действует
на классах изоморфных строго проективных левых $A$-модулей. Опишем
стабилизирующие подгруппы этого действия.

#proposition[
  Пусть $A$~— произвольная $R$-алгебра, $Q$~— строго проективный левый
  $A$-модуль и $B = End_A (Q)^degree$. Тогда имеет место точная
  последовательность групп
  $
    1 -> InAut(B) -> Aut_(R hyph alg)(B) #map-arrow($delta_Q$) Pic_R (A),
  $ <eq:picard-stabilizer-sequence>
  где
  $
    Im delta_Q = {[P] in Pic_R (A) | P tensor_A Q tilde.eq Q
      " как левые " A "-модули"}.
  $
] <prop:picard-stabilizer>

#proof[
  Предположим сначала, что $Q = A$ и, значит, $B = A$. Определим
  $delta_A (alpha) = [attach(A, bl: 1, br: alpha)]$. Из предложения
  @prop:picard-twisted-bimodules следует, что $delta_A$~— гомоморфизм (п.
  @cond:twisted-bimodule-tensor-product), что последовательность
  @eq:picard-stabilizer-sequence точна (п. @cond:twisted-bimodule-inner) и что
  $Im(delta_A)$ может быть описан указанным образом (п.
  @cond:twisted-bimodule-free-left-module).

  В общем случае положим $Q^* = Hom_A (Q, A)$. Тогда
  $T = Hom_A (Q, dot) tilde.eq Q^* tensor_A dot:
  A hyph moduleCategory -> B hyph moduleCategory$ является эквивалентностью, для
  которой $T Q = B$ и которая индуцирует изоморфизм $h: Pic_R (A) -> Pic_R (B)$,
  где $h[P] = [Q^* tensor_A P tensor_A Q]$. Определим теперь $delta_Q$ как
  композицию
  $
    Aut_(R hyph alg)(B) #map-arrow($delta_B$) Pic_R (B)
    #map-arrow($h^(-1)$) Pic_R (A).
  $
  Следовательно, $Ker(delta_Q) = Ker(delta_B) = InAut(B)$, и поэтому
  последовательность точна. Если $P in PicCat_R (A)$, то
  [$P tensor_A Q tilde.eq Q$ как левые $A$-модули] $<=>$
  [$Q^* tensor_A P tensor_A Q tilde.eq Q^* tensor_A Q$ как левые $B$-модули].
  Так как $Q^* tensor_A Q tilde.eq B$ как бимодули, то это означает, что
  [$P tensor_A Q tilde.eq Q$ как левые $A$-модули] $<=> [h[P] in Im(delta_B)]$.
  Это устанавливает сформулированное описание для $Im(delta_Q)$, завершая
  доказательство предложения.
]

В том случае, когда $P in PicCat_R (A)$, элементы из центра $C$ кольца $A$ не
обязаны действовать одинаково справа и слева на $P$. Если $t in C$, то
$p arrow.r.bar p t$, будучи эндоморфизмом бимодуля $P$, является умножением
слева на однозначно определенный элемент $alpha_P (t)$, который должен опять
лежать в $C$. Таким образом, получаем отображение, очевидно являющееся
гомоморфизмом $R$-алгебр:
$
  alpha_P: C -> C; quad p t = alpha_P (t) p quad (p in P, t in C).
$
Например, если $P = attach(A, bl: 1, br: alpha)$
$(alpha in Aut_(R hyph alg)(A))$, то $alpha_P = alpha bar.v C$.

Предположим, что $P, Q in PicCat_R (A)$. Тогда для $p in P$, $q in Q$ и $t in C$
справедливы равенства:
$
  (p tensor q) t = p tensor alpha_Q (t) q = p alpha_Q (t) tensor q
  = alpha_P (alpha_Q (t)) p tensor q.
$
#source(74)Таким образом,
$
  alpha_(P tensor_A Q) = alpha_P alpha_Q.
$
Очевидно, что $alpha_A = 1_C$, и поэтому из обратимости модуля $P$ следует, что
$alpha_P$ является автоморфизмом. Итак, мы доказали:

#proposition[
  Пусть $A$ есть $R$-алгебра с центром $C$. Тогда имеет место точная
  последовательность
  $
    0 -> Pic_C (A) -> Pic_R (A) #map-arrow($h$) Aut_(R hyph alg)(C),
  $
  где $h[P] = alpha_P$. Если алгебра $A$ коммутативна, то последовательность
  $
    0 -> Pic_A (A) -> Pic_R (A) #map-arrow($h$) Aut_(R hyph alg)(A) -> 1
  $
  точна и гомоморфизм $h$ расщепляем с помощью отображения
  $alpha arrow.r.bar [attach(A, bl: 1, br: alpha)]$ (см. предложение
  @prop:picard-twisted-bimodules).
] <prop:picard-center-exact-sequence>

*Пример.* Пусть $A$~— кольцо целых алгебраических чисел в конечном расширении
$L$ поля $upright(bold(Q))$. Пусть $G$~— группа (Галуа) автоморфизмов поля $L$.
Очевидно, что можно отождествить $G$ с $Aut_(Int hyph alg)(A)$, и поэтому группа
$Pic_Int (A)$ является полупрямым произведением группы $G$ с группой
$Pic_A (A)$, которая, как известно, изоморфна группе классов идеалов кольца $A$
(см. гл.~@ch:rings-modules, §~@sec:rank-picard-krull). При этом изоморфизме
действие $G$ на группе $Pic_A (A)$ соответствует очевидному действию
автоморфизмов поля на классах идеалов.

Если мы возьмем такое описание автоэквивалентностей категории
$A hyph moduleCategory$, то обнаружим, что группа
$Pic_Int (A hyph moduleCategory)$ конечна (относительно конечности числа классов
см. §~@sec:finiteness-of-class-number гл.~@ch:arithmetic-finiteness). В
частности, $Pic_Int (Int hyph moduleCategory) = {1}$, т. е. любая
автоэквивалентность категории абелевых групп изоморфна тождественному функтору.
