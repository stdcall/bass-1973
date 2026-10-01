#import "main-defs.typ": (
  Div, Im, SK, U, char, idx, maxSpec, mennicke, name-idx, source, supp,
  symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, lemma, named-axiom,
  proof, proposition, theorem, variant-condition,
)

#heading(level: 2)[Законы взаимности над дедекиндовыми кольцами, их
  эквивалентность символам Меннике] <sec:dedekind-reciprocity-laws>

_В этом параграфе через $frak(q)$ обозначается ненулевой идеал дедекиндова
кольца $A$._ Пусть $X = maxSpec(A)$. Для $frak(p) in X$ введем группу

$
  U_frak(p) (frak(q)) tilde.eq U(frac(A, frak(p) frak(q)),
    frac(frak(q), frak(p) frak(q)))
  = {"обратимые элементы кольца" quad frac(A, frak(p) frak(q)),
    quad "сравнимые с" quad 1 mod frac(frak(q), frak(p) frak(q))}.
$
#symbol-idx($U_frak(p) (frak(q))$, sort: "U_p(q)", group: "groups", order: 125)

#source(253)Описание этой группы зависит от того, делится $frak(q)$ на $frak(p)$
или нет.

_Случай $frak(p) divides.not frak(q)$._ В силу китайской теоремы об остатках
$frac(A, frak(p) frak(q)) = frac(A, frak(p)) times frac(A, frak(q))$, а из
соответствующего прямого разложения для $U(frac(A, frak(p) frak(q)))$ вытекает
канонический изоморфизм

$ U_frak(p) (frak(q)) tilde.eq U(frac(A, frak(p))). $
<eq:reciprocity-unramified-unit-group>

_Случай $frak(p) divides frak(q)$._ Можем записать
$frak(q) = frak(p)^h frak(q)'$, где $frak(q)'$ и $frak(p)$ взаимно просты и
$h = v_frak(p) (frak(q)) > 0$. В этом случае
$frac(A, frak(p) frak(q)) = frac(A, frak(p)^(h + 1)) times frac(A, frak(q)')$, и
мы получаем канонический изоморфизм

$
  U_frak(p) (frak(q)) tilde.eq U(frac(A, frak(p)^(h + 1)),
    frac(frak(p)^h, frak(p)^(h + 1))) quad (h = v_frak(p) (frak(q)) > 0).
$

Так как квадрат идеала $frak(a) = frac(frak(p)^h, frak(p)^(h + 1))$ равен $0$,
то отображение $a arrow.r.bar a + 1$ осуществляет изоморфизм аддитивной группы
идеала $frak(a)$ и мультипликативной группы $1 + frak(a)$. Таким образом

$
  U_frak(p) (frak(q)) tilde.eq 1 + frac(frak(p)^h, frak(p)^(h + 1))
  tilde.eq frac(frak(p)^h, frak(p)^(h + 1))
  quad (h = v_frak(p) (frak(q)) > 0).
$ <eq:reciprocity-ramified-unit-group>

Этот модуль не меняется при локализации кольца $A_frak(p)$, являющегося кольцом
дискретного нормирования, и, следовательно,

$ frac(frak(p)^h, frak(p)^(h + 1)) tilde.eq frac(A, frak(p)) $
<eq:reciprocity-residue-additive-group>

(изоморфизм не канонический).

Заметим теперь, что группа $U_frak(p) (frak(q))$ изоморфна _мультипликативной_
группе кольца $frac(A, frak(p))$, если $frak(p) divides.not frak(q)$, и
_аддитивной_ группе кольца $frac(A, frak(p))$, если $frak(p) divides frak(q)$.

Через $U'_frak(p) (frak(q))$ обозначим полный прообраз в кольце $A$ группы
$U_frak(p) (frak(q))$. Таким образом, $U'_frak(p) (frak(q))$ является множеством
таких элементов $a in A$, что $a in.not frak(p)$ и $a equiv 1 mod frak(q)$. Если
$chi: U_frak(p) (frak(q)) -> C$ — гомоморфизм и $a in U'_frak(p) (frak(q))$, то
мы позволим себе через $chi(a)$ обозначать значение гомоморфизма $chi$ на
смежном классе элемента $a$ группы $U_frak(p) (frak(q))$.

Ниже мы собираемся показать, что символы Меннике $[ ]: W_frak(q) -> C$
эквивалентны следующим объектам:

#definition[
  $frak(q)$-взаимностью#idx("q-взаимность") со значениями в абелевой группе $C$
  называется совокупность ${chi_frak(p) | frak(p) in X}$ гомоморфизмов
  $ chi_frak(p): U_frak(p) (frak(q)) -> C, $
  удовлетворяющих приводимым ниже условиям
  @ax:reciprocity-vanishing-normalization и @ax:reciprocity-product-formula.

  #named-axiom[
    Если $a in U'_frak(p) (frak(q))$, то
    $chi_frak(p) (a)^(v_frak(p) (1 - a)) = 1$.
  ] <ax:reciprocity-vanishing-normalization>
  #named-axiom[
    Если $a equiv 1 mod frak(q)$, $a A + b A = A$; $a != 0 != b$, то
    $
      product_(frak(p) divides b) chi_frak(p) (a)^(v_frak(p) (b))
      = product_(frak(p) divides a) chi_frak(p) (b)^(v_frak(p) (a)).
    $ <eq:reciprocity-product-formula>
  ] <ax:reciprocity-product-formula>
] <def:dedekind-reciprocity>

#source(254)Последняя аксиома требует некоторого пояснения. Если
$frak(p) divides b$, то $a in.not frak(p)$ и поэтому
$a in U'_frak(p) (frak(q))$, а следовательно, левая часть равенства имеет смысл.
С другой стороны, если $frak(p) divides a$, то $frak(p) divides.not frak(q)$,
так как $a equiv 1 mod frak(q)$. Следовательно, в этом случае у нас имеется
канонический изоморфизм $U_frak(p) (frak(q)) tilde.eq U(frac(A, frak(p)))$ (см.
@eq:reciprocity-unramified-unit-group), и $b$ ($in.not frak(p)$) представляет
собой элемент этой группы. Именно в этом смысле мы интерпретируем правую часть
равенства @eq:reciprocity-product-formula. В том случае, когда один из элементов
$a$ или $b$ равен $0$, другой элемент обратим. В этом случае одна часть
равенства @eq:reciprocity-product-formula представляет собой пустое произведение
(и, следовательно, $= 1$), а все показатели в другой части равенства равны $0$
(и, следовательно, она также равна $1$).

Условие @ax:reciprocity-vanishing-normalization автоматически выполнено в том
случае, когда $frak(p) divides.not frak(q)$, как это вытекает из следующего
результата.

#proposition[
  Пусть ${chi_frak(p)}$ — совокупность гомоморфизмов из
  @def:dedekind-reciprocity. Тогда условие
  @ax:reciprocity-vanishing-normalization эквивалентно каждому из условий:

  #named-axiom[
    Если $a in U'_frak(p) (frak(q))$, то
    $chi_frak(p) (a^(v_frak(p) (frak(q)))) = 1$.
  ] <ax:reciprocity-exponent-normalization>
  #named-axiom[
    Если $v_frak(p) (frak(q))$ не делится на $char(frac(A, frak(p)))$, то
    $chi_frak(p)$ — тривиальный гомоморфизм.
  ] <ax:reciprocity-residue-characteristic-normalization>
] <prop:reciprocity-normalization-equivalences>

#proof[
  @ax:reciprocity-vanishing-normalization $==>$
  @ax:reciprocity-exponent-normalization. Пусть $h = v_frak(p) (frak(q))$ и
  $a in U'_frak(p) (frak(q))$. Надо рассмотреть лишь случай $h > 0$. Если
  $v_frak(p) (1 - a) = h$, то условие @ax:reciprocity-exponent-normalization
  совпадает с @ax:reciprocity-vanishing-normalization. Но если
  $v_frak(p) (1 - a) > h$, то $a equiv 1 mod frak(p) frak(q)$ и поэтому в этом
  случае уже $chi_frak(p) (a) = 1$.

  @ax:reciprocity-exponent-normalization $==>$
  @ax:reciprocity-vanishing-normalization. Пусть $h$ и $a$ выбраны, как и
  прежде. Сначала допустим, что $h = 0$. Если $v_frak(p) (1 - a) = 0$, то ничего
  доказывать не надо. Если $v_frak(p) (1 - a) > 0$, то $a equiv 1 mod frak(p)$
  и, следовательно, $a equiv 1 mod frak(p) frak(q)$, а потому
  $chi_frak(p) (a) = 1$.

  Предположим далее, что $h > 0$. Тогда, как и выше, условия
  @ax:reciprocity-vanishing-normalization и
  @ax:reciprocity-exponent-normalization совпадают, если
  $v_frak(p) (1 - a) = h$. В противном случае $a equiv 1 mod frak(p) frak(q)$ и
  поэтому уже $chi_frak(p) (a) = 1$.

  @ax:reciprocity-exponent-normalization $<=>$
  @ax:reciprocity-residue-characteristic-normalization. Если
  $frak(p) divides.not frak(q)$, то ни одна из аксиом не утверждает ничего
  нетривиального. Предположим поэтому, что $frak(p) divides frak(q)$. В этом
  случае $U_frak(p) (frak(q)) = frac(A, frak(p))$ (в правой части
  рассматривается аддитивная группа, см. @eq:reciprocity-ramified-unit-group и
  @eq:reciprocity-residue-additive-group выше) и из
  @ax:reciprocity-exponent-normalization утверждается, что экспонента для
  $Im(chi_frak(p))$ равна $h = v_frak(p) (frak(q)) > 0$. Если
  $char(frac(A, frak(p))) = 0$, то группа $frac(A, frak(p))$ делимая, и поэтому
  у нее нет нетривиальных факторгрупп конечной экспоненты. Если же
  $char(frac(A, frak(p))) = p > 0$, то группа $frac(A, frak(p))$ может иметь
  нетривиальную факторгруппу экспоненты $h$ тогда и только тогда, когда $p$
  делит $h$. Таким образом, устанавливается эквивалентность
  @ax:reciprocity-exponent-normalization и
  @ax:reciprocity-residue-characteristic-normalization. Доказательство
  завершено.
]

#source(255)
#theorem[
  Пусть $C$ — абелева группа. Тогда можно установить взаимно однозначное
  соответствие между символами Меннике $[ ]: W_frak(q) -> C$ и
  $frak(q)$-взаимностями ${chi_frak(p)}$ со значениями в $C$, определенными
  следующим образом:
  $
    chi_frak(p) (a) = mennicke(frak(p) frak(q), a)
    quad (a in U'_frak(p) (frak(q)))
  $
  и
  $
    mennicke(b, a) = product_(frak(p) divides b) chi_frak(p) (a)^(v_frak(p) (b))
    quad ((a, b) in W_frak(q), quad a != 0 != b).
  $
] <th:mennicke-reciprocity-equivalence>

Заметим, что мы использовали здесь предложение
@prop:mennicke-ideal-symbol-extension, в силу которого существуют символы
$mennicke(frak(p) frak(q), a)$. Это возможно, поскольку кольцо $A$ дедекиндово,
все ненулевые идеалы обратимы и поэтому все предположения
@prop:mennicke-ideal-symbol-extension для всех $frak(p) frak(q)$ выполнены.

#proof[
  Сначала предположим, что $[ ]: W_frak(q) -> C$ является символом Меннике.
  Продолжим его, как в @prop:mennicke-ideal-symbol-extension, до отображения
  $[ ]: overline(W)_frak(q) -> C$. Предположим, что $a equiv 1 mod frak(q)$ и
  $a != 0$. Если идеалы $frak(b)_1$ и $frak(b)_2$ комаксимальны с $a$ (и
  $!= 0$), то поскольку $mennicke(frak(q), a) = 1$ (см.
  @ax:mennicke-ideal-unit-denominator и
  @ax:mennicke-ideal-denominator-translation в
  @prop:mennicke-ideal-symbol-extension),
  $
    mennicke(frak(b)_1 frak(b)_2 frak(q), a)
    = mennicke(frak(b)_1 frak(b)_2 frak(q), a) mennicke(frak(q), a)
    = mennicke(frak(b)_1 frak(q) frak(b)_2 frak(q), a)
    = mennicke(frak(b)_1 frak(q), a) mennicke(frak(b)_2 frak(q), a).
  $
  Следовательно, для любого идеала $frak(b) != 0$, комаксимального с $a$,
  справедливо равенство
  $
    mennicke(frak(b) frak(q), a)
    = product_(frak(p) divides frak(b))
    mennicke(frak(p) frak(q), a)^(v_frak(p) (frak(b)))
    = product_(frak(p) divides frak(b)) chi_frak(p) (a)^(v_frak(p) (frak(b))),
  $
  где мы определили $chi_frak(p) (a)$ как $mennicke(frak(p) frak(q), a)$.
  Заметим, что $a in U'_frak(p) (frak(q))$ и $chi_frak(p) (a)$ зависит от $a$
  лишь по модулю $frak(p) frak(q)$ (в силу
  @ax:mennicke-ideal-denominator-translation). Следовательно, можно
  рассматривать $chi_frak(p)$ как отображение
  $ chi_frak(p): U_frak(p) (frak(q)) -> C, $
  которое в силу @ax:mennicke-ideal-denominator-multiplicativity является
  гомоморфизмом. Если в рассмотренной выше ситуации $frak(b) subset frak(q)$, то
  $
    mennicke(frak(b), a) = mennicke(frak(b) frak(q), a)
    = product_(frak(p) divides frak(b)) chi_frak(p) (a)^(v_frak(p) (frak(b))).
  $

  #source(256)
  Мы должны показать, что совокупность отображений ${chi_frak(p)}$ является
  $frak(q)$-взаимностью. Установим сначала
  @ax:reciprocity-vanishing-normalization. Как было отмечено в
  @prop:reciprocity-normalization-equivalences, эта аксиома автоматически
  выполняется, если $frak(p) divides.not frak(q)$. Следовательно, допустим, что
  $h = v_frak(p) (frak(q)) > 0$. Элемент из $U_frak(p) (frak(q))$ можно
  представлять себе как элемент $a in U'_frak(p) (frak(q))$, такой, что
  $a equiv 1 mod frak(p)' frak(q)$ для всех простых идеалов
  $frak(p)' != frak(p)$, делящих $frak(q)$. Таким образом,
  $chi_(frak(p)') (a) = 1$ для таких $frak(p)'$. Кроме того, как мы уже
  отмечали, $chi_(frak(p)_1) (a)^(v_(frak(p)_1) (1 - a)) = 1$, если
  $frak(p)_1 divides.not frak(q)$. Следовательно,
  $
    1 = mennicke(1 - a, a)
    = product_(frak(p)' divides 1 - a)
    chi_(frak(p)') (a)^(v_(frak(p)') (1 - a))
    = chi_frak(p) (a)^(v_frak(p) (1 - a)).
  $

  Далее, мы должны установить @ax:reciprocity-product-formula. Если
  $a equiv 1 mod frak(q)$, $b != 0$ и $a A + b A = A$, то мы утверждаем, что
  $
    product_(frak(p) divides b) chi_frak(p) (a)^(v_frak(p) (b))
    = product_(frak(p) divides a) chi_frak(p) (b)^(v_frak(p) (a)).
  $
  Это очевидно, если $a = 1$. Поэтому предположим, что $t = 1 - a != 0$. Тогда
  из формулы @eq:mennicke-square-transfer в доказательстве
  @prop:mennicke-axiom-redundancy следует, что
  $ mennicke(-a t, a + b t) = mennicke(b t^2, a) = mennicke(b t, a). $
  Раскрывая каждую часть этого равенства, получаем, что
  $
    mennicke(b t, a)
    = product_(frak(p) divides b t) chi_frak(p) (a)^(v_frak(p) (b t))
    = product_(frak(p) divides b) chi_frak(p) (a)^(v_frak(p) (b))
    mennicke(t, a),
  $
  с $mennicke(t, a) = 1$, и
  $
    mennicke(-a t, a + b t)
    = product_(frak(p) divides a t) chi_frak(p) (a + b t)^(v_frak(p) (a t))
    = product_(frak(p) divides a) chi_frak(p) (a + b t)^(v_frak(p) (a))
    mennicke(t, a + b t),
  $
  с $mennicke(t, a + b t) = 1$. Если $frak(p) divides a$, то $chi_frak(p)$
  зависит лишь от смежного класса по модулю $frak(p)$ и, следовательно, лишь от
  смежного класса по модулю $a$. Так как
  $a + b t = a + b (1 - a) equiv b mod a$, то получаем, что
  $chi_frak(p) (a + b t) = chi_frak(p) (b)$, если $frak(p) divides a$. Таким
  образом, из трех рассмотренных выше равенств следует
  @ax:reciprocity-product-formula.

  Обратно, предположим, что ${chi_frak(p)}$ является $frak(q)$-взаимностью со
  значениями в $C$. Если $a equiv 1 mod frak(q)$ и идеал $frak(b) != 0$
  комаксимален с $a$, то положим
  $
    mennicke(frak(b), a)
    = product_(frak(p) divides frak(b)) chi_frak(p) (a)^(v_frak(p) (frak(b)))
    = product_(frak(p) divides.not a) chi_frak(p) (a)^(v_frak(p) (frak(b))).
  $

  #source(257)
  Очевидно, что $mennicke(frak(b), 1) = 1$ и отображение $mennicke(frak(b), a)$
  бимультипликативно по $(a, frak(b))$. Далее, мы утверждаем, что если
  $frak(b) subset frak(q)$, то
  $
    mennicke(frak(b), a + b) = mennicke(frak(b), a)
    quad "для всех" quad b in frak(b).
  $
  На самом деле мы покажем, что $chi_frak(p) (a + b)^(v_frak(p) (frak(b)))
  = chi_frak(p) (a)^(v_frak(p) (frak(b)))$ для всех $frak(p)$, делящих
  $frak(b)$. Если $frak(p) divides.not frak(q)$, то это следует из того, что
  $a equiv a + b mod frak(p)$, поскольку в этом случае $chi_frak(p)$ зависит
  лишь от смежного класса по модулю $frak(p)$. Таким образом, предположим, что
  $v_frak(p) (frak(q)) = h > 0$. Если $v_frak(p) (b) > h$, то
  $a + b equiv a mod frak(p) frak(q)$, и поэтому
  $chi_frak(p) (a + b) = chi_frak(p) (a)$. Если $v_frak(p) (frak(b)) = h$, то из
  @ax:reciprocity-exponent-normalization следует, что
  $chi_frak(p) (a + b)^h = 1 = chi_frak(p) (a)^h$.

  Далее, если $(a, b) in W_frak(q)$, то определим
  $
    mennicke(b, a) = cases(
      mennicke(b A, a) & "если" quad b != 0,
      1 & "если" quad b = 0.
    )
  $
  Из сделанных выше замечаний легко следует, что этот символ мультипликативен по
  $a$ (@ax:mennicke-second-multiplicativity) и зависит от $a$ лишь по модулю $b$
  (@ax:mennicke-lower-transvection), причем допускается даже случай $b = 0$.
  Кроме того, очевидно, что если $(a, b_1), (a, b_2) in W_frak(q)$, то
  $mennicke(b_1 b_2, a) = mennicke(b_1, a) mennicke(b_2, a)$, как только
  $b_1 != 0 != b_2$ или $b_1 = 0 = b_2$. Следовательно, предположим, что
  $b_1 != 0 = b_2$. Тогда левая часть равенства равна 1, а правая часть равна
  $mennicke(b_1, a)$, где теперь $a in U(A)$, поскольку $(a, 0) in W_frak(q)$.
  Из @ax:reciprocity-product-formula, таким образом, следует, что
  $
    mennicke(b_1, a)
    = product_(frak(p) divides b_1) chi_frak(p) (a)^(v_frak(p) (b_1))
    = product_(frak(p) divides a) chi_frak(p) (b_1)^(v_frak(p) (a)) = 1.
  $
  Этим установлено @ax:mennicke-first-multiplicativity и, значит, выполнены все
  аксиомы символа Меннике, кроме @ax:mennicke-upper-transvection.

  Нам надо показать, что если $(a, b) in W_frak(q)$ и $t in frak(q)$, то
  $mennicke(b + t a, a) = mennicke(b, a)$. Если хотя бы один из элементов $b$
  или $b + t a$ равен нулю, то элемент $a$ обратим, и в этом случае, как мы
  видели выше, оба символа равны единице. Кроме того, если $a = 0$, то равенство
  является тождеством. В противном случае можно применить
  #source(258)
  @ax:reciprocity-product-formula и получить равенство
  $
    mennicke(b + t a, a)
    = product_(frak(p) divides b + t a)
    chi_frak(p) (a)^(v_frak(p) (b + t a))
    = product_(frak(p) divides a) chi_frak(p) (b + t a)^(v_frak(p) (a)).
  $
  Если $frak(p) divides a$, то $frak(p) divides.not frak(q)$ и потому
  $chi_frak(p)$ зависит лишь от смежного класса по модулю $frak(p)$ и,
  следовательно, лишь по модулю $a$. Таким образом, для таких $frak(p)$ имеем
  $chi_frak(p) (b + t a) = chi_frak(p) (b)$. Поэтому приведенная выше формула
  вместе с соответствующей формулой для $mennicke(b, a)$ показывают, что, как и
  утверждалось, $mennicke(b + t a, a) = mennicke(b, a)$.

  Итак, мы показали, что формулы в теореме @th:mennicke-reciprocity-equivalence
  действительно определяют отображение символов Меннике в $frak(q)$-взаимности,
  а также отображение в обратном направлении. Из приведенных выше рассуждений,
  очевидно, следует, что эти два отображения обратны друг другу. Это завершает
  доказательство теоремы @th:mennicke-reciprocity-equivalence.
]

Некоторые законы взаимности, встречающиеся в теории чисел и в алгебраической
геометрии, по традиции выражаются в виде «формул произведения». С целью
нахождения подобного описания для $frak(q)$-взаимностей, рассмотренных здесь,
введем некоторые _локальные символы_ (см. Серр @bib:Serre1959, гл. III, §1).
#idx("локальный символ")#name-idx("Серр (Serre J.-P.)")

Пусть $A$, $frak(q)$ и $X = maxSpec(A)$ выбраны, как и ранее. Пусть $L$ — поле
частных кольца $A$. Положим
$
  U_frak(q) (L) = {a in U(L) bar
    v_frak(p) (a - 1) >= v_frak(p) (frak(q)),
    quad "если" quad v_frak(p) (frak(q)) > 0}.
$
Это подгруппа группы $U(L)$. Если $frak(p) in X$, то определим _локальный
$frak(q)$-символ_ в $frak(p)$ как антисимметрическое билинейное (т.~е.
бимультипликативное) спаривание:
$ (;)_frak(p): U_frak(q) (L) times U(L) -> U_frak(p) (frak(q)); $
$
  (a, b)_frak(p) "— смежный класс элемента" quad c quad "в"
  quad U_frak(p) (frak(q)),
$
где $c = (-1)^(alpha beta) a^beta / b^alpha$, $alpha = v_frak(p) (a)$,
$beta = v_frak(p) (b)$.

Это определение требует некоторого комментария: надо убедиться в том, что $c$
действительно определяет смежный класс из $U_frak(p) (frak(q))$. Имеем:
$v_frak(p) (c) = beta v_frak(p) (a) - alpha v_frak(p) (b) = 0$, поэтому
$c in U(A_frak(p))$ и $U_frak(p) (frak(q)) = U(frac(A, frak(p)))
= U(frac(A_frak(p), frak(p) A_frak(p)))$, если $frak(p) divides.not frak(q)$.
Кроме того,
$
  c = cases(
    a^beta & "если" quad alpha = 0,
    b^(-alpha) & "если" quad beta = 0
  ).
$
<eq:local-reciprocity-symbol-unit-cases>
Наконец, предположим, что $v_frak(p) (frak(q)) = h > 0$. Тогда
$v_frak(p) (1 - a) >= h > 0$. Поэтому $alpha = 0$ и
$c = a^beta in 1 + frak(p)^h A_frak(p)$. Следовательно, смежный класс определен
в $U_frak(p) (frak(q)) tilde.eq 1 + frac(frak(p)^h, frak(p)^(h + 1))$.

#source(259)
Множитель $(-1)^(alpha beta)$ не будет играть в этом параграфе никакой роли. Мы
ввели его, чтобы согласовать наши обозначения с обозначениями Серра
@bib:Serre1959 (гл. III, §4).
#name-idx("Серр (Serre J.-P.)")

Если $frak(a)$ — дробный идеал кольца $A$ в $L$, то (см. @sec:rank-picard-krull)
$Div(frak(a)) = sum v_frak(p) (frak(a)) frak(p) in D(A)$. В частности,
$Div(a) = Div(a A)$ для $a in U(L)$. _Носителем_ дивизора
$frak(d) = sum n_frak(p) frak(p)$ называется множество тех $frak(p) in X$, для
которых $n_frak(p) != 0$; он обозначается через $supp(frak(d))$.
#idx("носитель дивизора")

Пусть $(a, b) in U_frak(q) (L) times U(L)$. Тогда из приведенной выше формулы
@eq:local-reciprocity-symbol-unit-cases следует, что $(a, b)_frak(p) = 1$, если
$frak(p) in.not supp(Div(a)) union supp(Div(b))$ (последнее множество конечно).
Следовательно, можно определить
$ ((a, b)) = ((a, b)_frak(p))_(frak(p) in X) in Sigma, $
где
$ Sigma = product.co_(frak(p) in X) U_frak(p) (frak(q)). $

#theorem[
  Пусть $C$ — абелева группа, и пусть $chi: Sigma -> C$ — гомоморфизм,
  соответствующий семейству гомоморфизмов
  ${chi_frak(p): U_frak(p) (frak(q)) -> C bar frak(p) in X}$. Тогда следующие
  условия эквивалентны:
  #condition-list[
    #condition-item(format: "cyrillic")[Семейство ${chi_frak(p)}$ является
      $frak(q)$-взаимностью.] <cond:reciprocity-family>
    #condition-item(format: "cyrillic")[
      #named-axiom[Если $a in U_frak(q) (L)$ и $a != 1$, то
        $chi_frak(p) ((a, 1 - a)_frak(p)) = 1$ для всех $frak(p) in X$.]
      <ax:reciprocity-local-steinberg>
      #named-axiom[Для всех
        $
          (a, b) in V = {(a, b) in U_frak(q) (L) times U(L) bar
            supp(Div(a)) inter supp(Div(b)) = emptyset}
        $
        справедливо равенство
        $ product_(frak(p) in X) chi_frak(p) ((a, b)_frak(p)) = 1. $
        <eq:local-reciprocity-product-formula>
      ] <ax:reciprocity-disjoint-product>
    ] <cond:reciprocity-local-product-conditions>
    #variant-condition[
      #named-axiom[Гомоморфизмы $chi_frak(p)$ тривиальны, если только
        $v_frak(p) (frak(q))$ не является кратным числа
        $char(frac(A, frak(p)))$;] <ax:reciprocity-characteristic-vanishing>
      #named-axiom[Формула @eq:local-reciprocity-product-formula справедлива для
        всех $(a, b) in W_frak(q)$.] <ax:reciprocity-integral-product>
    ] <cond:reciprocity-integral-product-conditions>
  ]
] <th:reciprocity-product-formula-characterization>

#corollary[
  Существует канонический эпиморфизм $chi(frak(q)): Sigma -> SK_1 (A, frak(q))$,
  ядро которого порождается всеми $U_frak(p) (frak(q))$, для которых
  $v_frak(p) (frak(q))$ не является кратным числа $char(frac(A, frak(p)))$,
  вместе со всеми $((a, b))$, где $(a, b) in W_frak(q)$.
] <cor:universal-reciprocity-presentation>

#proof[
  Существует универсальный символ Меннике
  $[ ]_frak(q): W_frak(q) -> SK_1 (A, frak(q))$ (теорема
  @th:universal-mennicke-symbol-sk1). В силу теоремы
  #source(260)
  @th:mennicke-reciprocity-equivalence ему соответствует универсальная
  $frak(q)$-взаимность
  $
    {chi_frak(p) (frak(q)): U_frak(p) (frak(q)) -> SK_1 (A, frak(q))
      bar frak(p) in X}.
  $
  Эти отображения $chi_frak(p) (frak(q))$ определяют гомоморфизм
  $chi(frak(q)): Sigma -> SK_1 (A, frak(q))$. Из универсальности взаимности
  ${chi_frak(p) (frak(q))}$ следует, что если $chi: Sigma -> C$ — любой другой
  гомоморфизм, соответствующий $frak(q)$-взаимности, то
  $chi = h dot chi(frak(q))$ для однозначно определенного гомоморфизма
  $h: SK_1 (A, frak(q)) -> C$. Но теорема
  @th:reciprocity-product-formula-characterization утверждает, что проекция
  группы $Sigma$ на ее факторгруппу по подгруппе с указанными выше образующими
  является решением последней универсальной задачи. Следствие немедленно
  вытекает из этого замечания.
]

#proof(head: [Доказательство теоремы
  @th:reciprocity-product-formula-characterization.])[
  Если $a in U_frak(q) (L)$ и $a != 1$, то
  $
    (a, 1 - a)_frak(p) = cases(
      a^(v_frak(p) (1 - a)) & "если" quad v_frak(p) (a) = 0,
      1 & "в противном случае."
    )
  $
  Следовательно, @ax:reciprocity-local-steinberg совпадает в точности с
  @ax:reciprocity-vanishing-normalization, и очевидно, что
  @ax:reciprocity-characteristic-vanishing совпадает с
  @ax:reciprocity-residue-characteristic-normalization (см.
  @prop:reciprocity-normalization-equivalences).

  Если $(a, b) in V$, то можно записать равенство
  @eq:local-reciprocity-product-formula более подробно:
  $
    1 = (product_(frak(p) in supp(Div(b)))
      chi_frak(p) (a^(v_frak(p) (b)))) dot
    (product_(frak(p) in supp(Div(a)))
      chi_frak(p) (b^(-v_frak(p) (a)))),
  $
  $
    product_(frak(p) in supp(Div(b))) chi_frak(p) (a)^(v_frak(p) (b))
    = product_(frak(p) in supp(Div(a))) chi_frak(p) (b)^(v_frak(p) (a)).
  $
  <eq:reciprocity-disjoint-support-products>
  Таким образом, аксиома @ax:reciprocity-product-formula утверждает в точности
  то, что @eq:reciprocity-disjoint-support-products (т.~е.
  @eq:local-reciprocity-product-formula) справедливо для $(a, b) in W_frak(q)$,
  поэтому @ax:reciprocity-disjoint-product $=>$ @ax:reciprocity-product-formula
  $<=>$ @ax:reciprocity-integral-product.

  Остается показать, что если равенство @eq:local-reciprocity-product-formula
  справедливо для всех $(a, b) in W_frak(q)$, то оно справедливо для всех
  $(a, b) in V$. Формула @eq:local-reciprocity-product-formula может быть
  переписана более кратко в виде $chi((a, b)) = 1$. Так как функция
  $chi((a, b))$ билинейна (т.~е. бимультипликативна) по $(a, b)$, то теорема
  будет доказана, как только будет установлена
]

#lemma[
  Если $(a, b) in V$, то можно записать $a = a_1 a_2^(-1)$ и $b = b_1 b_2^(-1)$
  так, чтобы $(a_i, b_j) in W_frak(q)$ $(1 <= i, j <= 2)$.
] <lem:reciprocity-integral-factorization>

Действительно, тогда
$
  chi((a, b)) = chi((a_1, b_1)) chi((a_2, b_2))
  chi((a_1, b_2))^(-1) chi((a_2, b_1))^(-1) = 1.
$

#source(261)
#proof(head: [Доказательство леммы @lem:reciprocity-integral-factorization.])[
  Сначала будем искать элемент $a_2 in A$, для которого:
  #condition-list[
    #condition-item[$v_frak(p) (a_2) = -v_frak(p) (a)$, если
      $v_frak(p) (a) < 0$;] <cond:reciprocity-factor-denominator-valuations>
    #condition-item[$v_frak(p) (a_2) = 0$, если $v_frak(p) (b) != 0$;]
    <cond:reciprocity-factor-disjoint-valuations>
    #condition-item[$v_frak(p) (1 - a_2) >= v_frak(p) (frak(q))$, если
      $v_frak(p) (frak(q)) > 0$.] <cond:reciprocity-factor-congruence>
  ]
  Так как $v_frak(p) (1 - a) >= v_frak(p) (frak(q))$, если
  $v_frak(p) (frak(q)) > 0$, то $v_frak(p) (a) = 0$ для таких $frak(p)$.
  Следовательно, множества простых идеалов в
  @cond:reciprocity-factor-denominator-valuations и
  @cond:reciprocity-factor-congruence не пересекаются, а в
  @cond:reciprocity-factor-denominator-valuations и
  @cond:reciprocity-factor-disjoint-valuations они не пересекаются в силу
  предположения. Это, вообще говоря, не так для
  @cond:reciprocity-factor-disjoint-valuations и
  @cond:reciprocity-factor-congruence, но из условия в
  @cond:reciprocity-factor-congruence следует условие в
  @cond:reciprocity-factor-disjoint-valuations для любого простого идеала,
  входящего в оба множества. Следовательно, мы можем подобрать такой элемент
  $a_2$ (китайская теорема об остатках). Положим $a_1 = a a_2$. Тогда
  $v_frak(p) (a_1) = v_frak(p) (a) + v_frak(p) (a_2) >= 0$ для всех $frak(p)$ (в
  силу @cond:reciprocity-factor-denominator-valuations). Так как
  $A = inter_(frak(p) in X) A_frak(p)$, то $a_1 in A$. Далее,
  $v_frak(p) (1 - a_1) >= v_frak(p) (frak(q))$, если $v_frak(p) (frak(q)) >= 0$,
  так как это верно для $a$ и $a_2$ (в силу
  @cond:reciprocity-factor-congruence). Таким образом,
  $a_1 equiv 1 equiv a_2 mod frak(q)$. Кроме того, из
  @cond:reciprocity-factor-disjoint-valuations следует, что
  $supp(Div(a_2)) inter supp(Div(b)) = emptyset$, и поэтому это же верно и для
  $a_1$.

  Далее будем искать элемент $b_2 in A$, для которого:
  $ v_frak(p) (b_2) = -v_frak(p) (b), quad "если" quad v_frak(p) (b) < 0; $
  $
    v_frak(p) (b_2) = 0, quad "если" quad
    v_frak(p) (a_1) != 0 quad "или" quad v_frak(p) (a_2) != 0.
  $
  Эти условия независимы, как мы уже отмечали выше, и поэтому в силу китайской
  теоремы об остатках такой элемент $b_2$ существует. Рассуждая, как и ранее,
  убеждаемся в том, что $b_1 = b b_2 in A$ и что
  $supp(Div(b_j)) inter supp(Div(a_i)) = emptyset$ $(1 <= i, j <= 2)$. Это
  доказывает лемму.
]
