#import "main-defs.typ": Im, U, idx, mennicke, source, symbol-idx
#import "statements.typ": lemma, named-axiom, proof, proposition

== Символы Меннике $mennicke(frak(b), a)$ <sec:relative-mennicke-symbols>

_Зафиксируем в этом параграфе нётерову область целостности $A$ размерности
$<= 1$ и идеал $frak(q) != 0$ кольца $A$._ Мы хотим построить, исходя из символа
Меннике#idx("символ Меннике") $[ ]: W_frak(q) -> C$, символ
$(a, frak(b)) arrow.r.bar mennicke(frak(b), a)$#symbol-idx(
  $mennicke(a, frak(b))$,
  sort: "[a/upright b]",
  group: "delimiters",
  order: 162,
), #source(249)$overline(W)_frak(q) -> C$, где

$
  overline(W)_frak(q) = {(a, frak(b)) | a equiv 1 mod frak(q);
    frak(b) "— обратимый идеал", quad frak(b) subset frak(q);
    a A + frak(b) = A}.
$
#symbol-idx(
  $overline(W)_frak(q)$,
  sort: "overline W_q",
  group: "groups",
  order: 128,
)

#proposition[
  Существует отображение $[ ]: overline(W)_frak(q) -> C$, удовлетворяющее
  следующим условиям:

  #named-axiom[
    Если $(a, b) in W_frak(q)$ и $b != 0$, то
    $mennicke(b A, a) = mennicke(b, a)$.
  ] <ax:mennicke-ideal-principal-normalization>
  #named-axiom[
    $mennicke(frak(b), 1) = 1$ для всех $(1, frak(b)) in overline(W)_frak(q)$.
  ] <ax:mennicke-ideal-unit-denominator>
  #named-axiom[
    $mennicke(frak(b), a + b) = mennicke(frak(b), a)$ для всех
    $(a, frak(b)) in overline(W)_frak(q)$ и $b in frak(b)$.
  ] <ax:mennicke-ideal-denominator-translation>
  #named-axiom[
    $mennicke(frak(b)_1 frak(b)_2, a)
    = mennicke(frak(b)_1, a) mennicke(frak(b)_2, a)$ для всех $(a, frak(b)_1)$,
    $(a, frak(b)_2) in overline(W)_frak(q)$.
  ] <ax:mennicke-ideal-numerator-multiplicativity>
  #named-axiom[
    $mennicke(frak(b), a_1 a_2)
    = mennicke(frak(b), a_1) mennicke(frak(b), a_2)$ для всех $(a_1, frak(b))$,
    $(a_2, frak(b)) in overline(W)_frak(q)$.
  ] <ax:mennicke-ideal-denominator-multiplicativity>

  Кроме того, это отображение однозначно определяется условиями
  @ax:mennicke-ideal-principal-normalization,
  @ax:mennicke-ideal-unit-denominator и
  @ax:mennicke-ideal-denominator-translation и
  @ax:mennicke-ideal-numerator-multiplicativity.
] <prop:mennicke-ideal-symbol-extension>

Для доказательства нам потребуется следующая

#lemma[
  Пусть $frak(b)$ — обратимый идеал, и пусть $frak(a)$ — произвольный ненулевой
  идеал кольца $A$. Тогда существует обратимый идеал $frak(c)$, комаксимальный с
  $frak(a)$ и такой, что идеал $frak(b) frak(c)$ — главный.
] <lem:invertible-ideal-comaximal-representative>

#proof[
  Пусть $P = frak(b)^(-1)$, и пусть $S^(-1) A$ — (полу)локализация кольца $A$ по
  (взятым в конечном числе) максимальным идеалам, содержащим идеал $frak(a)$.
  Так как кольцо $S^(-1) A$ полулокально, то $S^(-1) P tilde.eq S^(-1) A$.
  Отсюда вытекает существование гомоморфизма $h: P -> A$, для которого
  $S^(-1) h$ — изоморфизм. Тогда
  $frak(c) = Im(h) tilde.eq P tilde.eq frak(b)^(-1)$ не содержится ни в каком
  максимальном идеале, содержащем идеал $frak(a)$.
]

#proof(head: [Доказательство предложения
  @prop:mennicke-ideal-symbol-extension.])[
  _Единственность._ Если $(a, frak(b)) in overline(W)_frak(q)$, то положим
  $t = 1 - a in frak(q)$. Если $t = 0$, то в силу
  @ax:mennicke-ideal-unit-denominator $mennicke(frak(b), a) = 1$. В противном
  случае воспользуемся леммой @lem:invertible-ideal-comaximal-representative и
  найдем идеал $frak(c)$, комаксимальный с $t frak(b)$ и такой, что
  $frak(b) frak(c) = d A$ для некоторого элемента $d in A$. В силу #source(
    250,
  )китайской теоремы об остатках можно подобрать $a'$ так, чтобы
  $ a' equiv a mod (frak(b) inter t A), quad a' equiv 1 mod frak(c). $
  Так как $a' equiv a equiv 1 mod t A$, то
  $a' equiv 1 mod (t A inter frak(c)) (= t frak(c))$. Таким образом,
  $
    mennicke(frak(b), a) = mennicke(frak(b), a') mennicke(t frak(c), a')
    = mennicke(t frak(b) frak(c), a') = mennicke(d t, a')
    = mennicke(d, a') mennicke(t, a') = mennicke(d, a').
  $
  Первое равенство следует из @ax:mennicke-ideal-denominator-translation и
  @ax:mennicke-ideal-unit-denominator, второе — из
  @ax:mennicke-ideal-numerator-multiplicativity, третье — из
  @ax:mennicke-ideal-principal-normalization.

  _Существование._ Определим $mennicke(frak(b), a)$ так, как это записано выше.
  Если $t = 0$, то никаких трудностей не возникает. Поэтому допустим, что
  $t != 0$. Так как элемент $a'$ определен сравнениями однозначно по модулю
  $(frak(b) inter t A) frak(c)$ и, следовательно, по модулю
  $d A = frak(b) frak(c)$, то $mennicke(d, a')$ не зависит от выбора элемента
  $a'$ при данном выборе идеала $frak(c)$. Кроме того, элемент $d$ определен с
  точностью до обратимого множителя, но эта замена не изменяет
  $mennicke(d, a')$.

  Предположим, что идеалы $frak(c)_1$ и $frak(c)_2$ удовлетворяют приведенным
  выше условиям на идеал $frak(c)$. Пусть $frak(c)_i frak(b) = d_i A$
  ($i = 1, 2$). Выберем идеал $frak(b)'$, комаксимальный с
  $frak(c)_1 frak(c)_2 frak(b) t$ и принадлежащий тому же классу идеалов, что и
  $frak(b)$, так что $frak(b)' frak(c)_i = e_i A$, где $e_i in A$ ($i = 1, 2$).
  Это возможно в силу @lem:invertible-ideal-comaximal-representative. Выберем
  теперь элемент $a'$ так, чтобы
  $
    a' equiv a mod (frak(b) inter t A), quad
    a' equiv 1 mod frak(c)_1 frak(c)_2 frak(b)'.
  $
  Заметим, что $frak(c)_1 frak(c)_2 frak(b)' = frak(c)_1 e_2 = frak(c)_2 e_1$ и
  $frak(b) t$ взаимно просты. Так как $a' equiv a equiv 1 mod t A$, то
  $a' equiv 1 mod e_i t$ ($i = 1, 2$). Таким образом,
  $
    mennicke(d_1, a') = mennicke(d_1, a') mennicke(e_2 t, a')
    = mennicke(d_1 e_2 t, a') quad "и" quad
    mennicke(d_2, a') = mennicke(d_2 e_1 t, a').
  $
  Но $d_1 e_2 A = (frak(c)_1 frak(b))(frak(c)_2 frak(b)')
  = (frak(c)_2 frak(b))(frak(c)_1 frak(b)') = d_2 e_1 A$, и поэтому
  $d_1 e_2 = u d_2 e_1$ для некоторого #source(251)элемента $u in U(A)$.
  Следовательно,
  $
    mennicke(d_1, a') = mennicke(d_1 e_2 t, a') = mennicke(u d_2 e_1 t, a')
    = mennicke(d_2 e_1 t, a') mennicke(u t, a') = mennicke(d_2, a'),
  $
  поскольку $a' equiv 1 mod t A (= u t A)$. Это показывает, что приведенное
  отображение $[ ]: overline(W)_frak(q) -> C$ определено корректно. Остается
  проверить выполнение аксиом.

  @ax:mennicke-ideal-principal-normalization Если $frak(b) = b A$, то в
  приведенной конструкции можно взять $frak(c) = A$, $d = b$ и $a' = a$. Тогда
  $mennicke(b A, a) = mennicke(d, a') = mennicke(b, a)$.

  @ax:mennicke-ideal-unit-denominator Это часть определения.

  @ax:mennicke-ideal-denominator-translation Если
  $(a, frak(b)) in overline(W)_frak(q)$ и $b in frak(b)$, то нам надо показать,
  что $mennicke(frak(b), a + b) = mennicke(frak(b), a)$. Пусть $a = 1 + t$
  ($t in frak(q)$). Выберем идеал $frak(c)$, комаксимальный с $frak(b) t$, если
  $t != 0$, и также с $frak(b)(t + b)$, если $t + b != 0$ (утверждение очевидно,
  если $t$ или $t + b$ — нулевой элемент), и такой, что $frak(b) frak(c) = d A$
  для некоторого элемента $d in A$. Выберем теперь $a'_1$ и $a'_2$ так, чтобы
  $
    a'_1 equiv a mod (frak(b) inter t A), quad
    a'_2 equiv (a + b) mod (frak(b) inter (t + b) A),
    quad a'_1 equiv 1 mod frak(c), quad a'_2 equiv 1 mod frak(c).
  $
  Тогда в силу определения $mennicke(frak(b), a) = mennicke(d, a'_1)$ и
  $mennicke(frak(b), a + b) = mennicke(d, a'_2)$. Но так как $b in frak(b)$, то
  $a'_1 equiv a equiv a'_2 mod frak(b)$, и
  $a'_1 equiv 1 equiv a'_2 mod frak(c)$. Следовательно,
  $a'_1 equiv a'_2 mod frak(b) frak(c) (= d A)$, и поэтому
  $mennicke(d, a'_1) = mennicke(d, a'_2)$.

  @ax:mennicke-ideal-numerator-multiplicativity Если $(a, frak(b)_1)$,
  $(a, frak(b)_2) in overline(W)_frak(q)$, то покажем, что
  $mennicke(frak(b)_1, a) mennicke(frak(b)_2, a)
  = mennicke(frak(b)_1 frak(b)_2, a)$. Если $a = 1$, то это следует из
  @ax:mennicke-ideal-unit-denominator. Поэтому допустим, что $t = 1 - a != 0$.
  Выберем идеал $frak(c)_i$, комаксимальный с $frak(b)_1 frak(b)_2 t$ и такой,
  что $frak(c)_i frak(b)_i = d_i A$ ($i = 1, 2$). Далее, выберем элемент $a'$
  так, чтобы
  $
    a' equiv a mod (frak(b)_1 frak(b)_2 inter t A), quad
    a' equiv 1 mod frak(c)_1 frak(c)_2.
  $
  Так как $frak(c)_1 frak(c)_2 frak(b)_1 frak(b)_2 = d_1 d_2 A$, то в силу
  определения
  $
    mennicke(frak(b)_1 frak(b)_2, a') = mennicke(d_1 d_2, a')
    = mennicke(d_1, a') mennicke(d_2, a')
    = mennicke(frak(b)_1, a) mennicke(frak(b)_2, a).
  $

  #source(252)@ax:mennicke-ideal-denominator-multiplicativity Если
  $(a_1, frak(b))$, $(a_2, frak(b)) in overline(W)_frak(q)$, то покажем, что
  $mennicke(frak(b), a_1 a_2) = mennicke(frak(b), a_1) mennicke(frak(b), a_2)$.
  Пусть $t_i = 1 - a_i$ ($i = 1, 2$) и $t = 1 - a_1 a_2$. Если $t_1 t_2 = 0$, то
  наше утверждение следует из @ax:mennicke-ideal-unit-denominator. Поэтому
  допустим, что $t_1 t_2 != 0$. Выберем идеал $frak(c)$, комаксимальный с
  $frak(b) t_1 t_2$ и с $t$, если $t != 0$, и такой, что $frak(c) frak(b) = d A$
  для некоторого $d in A$ (как в
  @lem:invertible-ideal-comaximal-representative). Выберем теперь элементы
  $a'_1$ и $a'_2$ таким образом, чтобы
  $
    a'_i equiv a_i mod frak(b) t_i
    quad ("и" quad mod frak(b) t_i t, quad "если" quad t != 0),
    quad a'_i equiv 1 mod frak(c) quad (i = 1, 2).
  $
  Тогда
  $
    mennicke(frak(b), a_1) mennicke(frak(b), a_2)
    = mennicke(d, a'_1) mennicke(d, a'_2) = mennicke(d, a'_1 a'_2).
  $
  Заметим, что $a'_1 a'_2 equiv a_1 a_2 mod frak(b)$ и
  $a'_1 a'_2 equiv 1 mod frak(c)$. Следовательно, если $a_1 a_2 = 1$, то
  $a'_1 a'_2 equiv 1 mod frak(b) frak(c) (= d A)$ и
  $mennicke(d, a'_1 a'_2) = 1 = mennicke(frak(b), a_1 a_2)$. В противном случае,
  т.~е. если $t != 0$, подберем элемент $a'$ так, чтобы
  $
    a' equiv a'_1 a'_2 mod (frak(b) inter t A), quad a' equiv 1 mod frak(c).
  $
  Тогда $a' equiv a'_1 a'_2 equiv a_1 a_2 mod (frak(b) inter t A)$, поэтому
  $mennicke(frak(b), a_1 a_2) = mennicke(d, a')$. Кроме того,
  $a' equiv a'_1 a'_2 mod frak(b) frak(c) (= d A)$, поэтому
  $mennicke(d, a') = mennicke(d, a'_1 a'_2)
  = mennicke(frak(b), a_1) mennicke(frak(b), a_2)$, что и требовалось доказать.
]

*Замечание.* Обычный символ Меннике $mennicke(b, a)$ равен $1$, если
$a in U(A)$. Однако вполне может случиться, что $mennicke(frak(b), a) != 1$,
даже если $a in U(A)$, когда идеал $frak(b)$ не является главным. Такие примеры
мы встретим в § @sec:curve-reciprocity.
