#import "main-defs.typ": (
  Div, E, Im, SK, SL, U, char, idx, maxSpec, name-idx, rad, source, supp,
  symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, named-axiom,
  numbered-formula-item, proof, proposition, theorem,
)

== Законы взаимности в числовых полях <sec:number-field-reciprocity>

_Пусть, как и в @sec:dedekind-reciprocity-laws: $A$ — дедекиндово кольцо,
$X = maxSpec(A)$, $L$ — поле частных кольца $A$ и $frak(q)$ — ненулевой идеал в
кольце $A$._ «Классические» $frak(q)$-взаимности, которые мы будем обсуждать в
этом и следующем параграфах, возникают из законов взаимности следующего типа.

Пусть $V = {v_frak(p) bar frak(p) in X}$, и пусть $S_infinity$ — множество
независимых нормирований поля $L$, неэквивалентных нормированиям из $V$. Пусть
$overline(V) = V union S_infinity$. Если $v in overline(V)$, то через $L_v$
обозначим пополнение поля $L$ в топологии, определенной нормированием $v$, и в
том случае, когда нормирование $v$ неархимедово, через $A_v$ обозначим кольцо
нормирования для $v$ в $L_v$. В последнем случае для #source(262)$t >= 0$ будем
использовать также обозначение
$ U_v (t) = {a in U(A_v) bar v(1 - a) >= t}. $
Таким образом, $U_v (0) = U(A_v)$, и $U_v (t)$ является подгруппой группы
$U(A_v)$ для $t >= 0$.

#definition[
  _Законом взаимности на $overline(V)$ со значениями в абелевой группе_
  $C$ назовем совокупность антисимметрических билинейных спариваний
  $
    lr((frac(dot, v))): U(L_v) times U(L_v) -> C
    quad (v in overline(V)),
  $
  для которых $lr((frac(a "," 1 - a, v))) = 1$, если $a, 1 - a in U(L_v)$,
  удовлетворяющих следующей «формуле произведения»:

  _если $a, b in U(L)$, то $lr((frac(a "," b, v))) = 1$ для всех, кроме
  конечного числа, $v in overline(V)$ и_
  $ product_(v in overline(V)) lr((frac(a "," b, v))) = 1. $
  <eq:number-field-reciprocity-product-formula>
] <def:number-field-reciprocity-law>
#idx("закон взаимности")#idx("формула произведения")
#symbol-idx(
  $lr((frac(dot, v)))$,
  sort: "(·/v)",
  group: "delimiters",
  order: 158,
)

Чтобы получить из такого закона взаимности $frak(q)$-взаимность, введем условие
#named-axiom[
  _если $frak(p) in X$ и $v = v_frak(p)$, то для $h = v(frak(q))$_
  $
    lr((frac(U_v (h + 1) "," U(L_v), v))) = {1}
    = lr((frac(U_v (h) "," U_v (0), v))).
  $
] <ax:reciprocity-local-filtration>

Далее, через $C_infinity$ обозначим подгруппу группы $C$, порожденную всеми
$
  lr((frac(a "," b, v))), quad "где" quad
  (a, b) in W_frak(q), quad v in S_infinity.
$
#symbol-idx($C_infinity$, sort: "C_∞", group: "letters", order: 75)

#proposition[
  Из условия @ax:reciprocity-local-filtration следует существование однозначно
  определенного гомоморфизма $f_frak(p): U_frak(p) (frak(q)) -> C$, такого, что
  $lr((frac(a "," b, v_frak(p)))) = f_frak(p) ((a, b)_frak(p))$ для
  $(a, b) in W_frak(q)$. Через $chi_frak(p)$ обозначим композицию отображений
  $
    U_frak(p) (frak(q)) arrow^(f_frak(p)) C
    arrow^("ест. гом.") frac(C, C_infinity).
  $
  Если условие @ax:reciprocity-local-filtration выполнено для всех
  $frak(p) in X$, то ${chi_frak(p) bar frak(p) in X}$ является
  $frak(q)$-взаимностью, индуцирующей гомоморфизм
  $SK_1 (A, frak(q)) -> frac(C, C_infinity)$, образ которого порождается
  элементами ${Im(chi_frak(p)) bar frak(p) in X}$.
] <prop:number-field-symbol-reciprocity>

#proof[
  Пусть $v = v_frak(p)$ и $h = v(frak(q))$. Выберем образующий $pi$
  максимального идеала кольца $A_v$. Из условия @ax:reciprocity-local-filtration
  #source(263)следует, что отображение $a |-> lr((frac(a "," pi, v)))$
  $(a in U_v (h))$ индуцирует гомоморфизм
  $ f_frak(p): U_frak(p) (frak(q)) = frac(U_v (h), U_v (h + 1)) -> C, $
  не зависящий от выбора элемента $pi$. Кроме того, если $b in U(L_v)$ и
  $beta = v(b)$, то $lr((frac(a "," b, v))) = lr((frac(a "," pi, v)))^beta
  = lr((frac(a^beta "," pi, v)))$.

  Предположим теперь, что $(a, b) in W_frak(q)$. Если $a in U_v (h)$ (что
  выполнено автоматически, если $h > 0$), то $(a, b)_frak(p)$ равно смежному
  классу в $U_frak(p) (frak(q))$ элемента $a^beta$, и поэтому
  $lr((frac(a "," b, v))) = f_frak(p) ((a, b)_frak(p))$. Если
  $a in.not U_v (h)$, то $h = 0$ и $b in U_v (0)$. Так как $lr((frac(dot, v)))$
  и $(;)_frak(p)$ антисимметричны, то
  $
    lr((frac(a "," b, v))) = lr((frac(b "," a, v)))^(-1)
    = f_frak(p) ((b, a)_frak(p))^(-1)
    = f_frak(p) ((a, b)_frak(p)).
  $
  Это доказывает первое утверждение предложения. Кроме того, из
  @lem:reciprocity-integral-factorization следует, что
  $lr((frac(a "," b, v))) = f_frak(p) ((a, b)_frak(p))$, как только
  $(a, b) in U_frak(q) (L) times U(L)$ и
  $supp(Div(a)) inter supp(Div(b)) = emptyset$, поскольку обе части равенства
  билинейны по $(a, b)$.

  Предположим, что условия @ax:reciprocity-local-filtration выполнены для всех
  $frak(p) in X$, и, как и выше, определим ${chi_frak(p)}$. Чтобы убедиться в
  том, что это $frak(q)$-взаимность, проверим условия
  @ax:reciprocity-local-steinberg и @ax:reciprocity-disjoint-product теоремы
  @th:reciprocity-product-formula-characterization. Для
  @ax:reciprocity-local-steinberg возьмем $a in U_frak(q) (L)$, $a != 1$. Тогда
  из определения @def:number-field-reciprocity-law и приведенной выше формулы
  следует, что $1 = lr((frac(a "," 1 - a, v_frak(p))))
  = f_frak(p) ((a, 1 - a)_frak(p))$ и, таким образом,
  $chi_frak(p) ((a, 1 - a)_frak(p)) = 1$ для всех $frak(p) in X$.

  В условие @ax:reciprocity-disjoint-product входит равенство
  $product_(frak(p) in X) chi_frak(p) ((a, b)_frak(p)) = 1$ для
  $(a, b) in W_frak(q)$. Из формулы @eq:number-field-reciprocity-product-formula
  в @def:number-field-reciprocity-law и приведенной формулы следует, что
  $
    1 = product_(v in overline(V)) lr((frac(a "," b, v)))
    = (product_(frak(p) in X) f_frak(p) ((a, b)_frak(p))) dot
    (product_(v in S_infinity) lr((frac(a "," b, v)))).
  $
  Это — равенство в группе $C$. При переходе к $frac(C, C_infinity)$ последний
  множитель исчезает и $f_frak(p)$ превращается в $chi_frak(p)$. Все доказано.
]

*Замечание.*
Для этого доказательства достаточно знать, что формула
@eq:number-field-reciprocity-product-formula из
@def:number-field-reciprocity-law справедлива лишь для $(a, b) in W_frak(q)$.

Допустим теперь, что $L$ — _числовое поле_, т.~е. конечное расширение поля $QQ$.
Пусть $S_infinity$#symbol-idx(
  $S_infinity$,
  sort: "S_∞",
  group: "groups",
  order: 117,
) — множество всех (неэквивалентных) #source(264)нормирований поля $L$, не
принадлежащих $V$. Предположим также, что $L$ содержит группу $mu_m$ корней
$m$-й степени из единицы. Тогда существует закон взаимности на $overline(V)$ со
значениями в $mu_m$, называемый _$m$-м степенным законом взаимности_; если
$m = 2$, то это обычный _квадратичный закон взаимности_ в числовых полях. Его
локальные символы обозначим через $lr((frac(dot, v)))_m$. Опишем теперь их в
ряде (на самом деле «в большинстве») случаев. (Весьма полная информация по всему
материалу этого параграфа содержится в добавлении к статье Басса, Милнора, Серра
@bib:Bass1967a). #idx(
  "m-й степенной закон взаимности",
)#idx(
  "квадратичный закон взаимности",
) #name-idx("Басс (Bass H.)")#name-idx("Милнор (Milnor J.)")
#name-idx("Серр (Serre J.-P.)")
#symbol-idx(
  $lr((frac(dot, v)))_m$,
  sort: "(·/v)_m",
  group: "delimiters",
  order: 159,
)

Пусть сначала $v$ — архимедово нормирование. Тогда:

если $v$ _комплексное_, то $L_v = CC$ и символ $lr((frac(dot, v)))_m$ тривиален;

если $v$ _вещественное_, то $L_v = RR$ и обязательно $m <= 2$;
$
  lr((frac(a "," b, v)))_2 = cases(
    -1 & "если" quad a "," b < 0,
    1 & "в противном случае."
  )
$

Пусть теперь нормирование $v$ _неархимедово_. Через $k(v)$ обозначим поле
вычетов кольца $A_v$. Оно является конечным полем характеристики $p$ из
$q = p^f$ элементов.

Если нормирование $v$ _неархимедово_ и $char(k(v)) divides.not m$, то группа
$mu_m subset A_v$ отображается инъективно в $k(v)$, и поэтому $U(k(v))$ —
циклическая группа порядка $q - 1 = m dot e$ (этим определяется число $e$).
Заметим, что
$
  lr((frac(a "," b, v)))_m equiv ((-1)^(alpha beta) a^beta / b^alpha)^e
  mod (rad A_v),
$
где $alpha = v(a)$, $beta = v(b)$. Это сравнение и включение
$lr((frac(a "," b, v)))_m in mu_m$ определяют символ. Например, если
$alpha = 0$, то $lr((frac(a "," b, v)))_m equiv a^(beta e)$, и поэтому если
элемент $b$ порождает $rad A_v$, то $lr((frac(a "," b, v)))_m = 1$ тогда и
только тогда, когда элемент $a$ является $m$-й степенью в поле $k(v)$. Таким
образом, мы восстановили «$m$-й степенной символ вычета».

Случай, когда $char(k(v)) divides m$, более сложен. Тем не менее символы также
существуют и в этом случае, и формула произведения
@eq:number-field-reciprocity-product-formula имеет место.

Рассматривая теперь идеал $frak(q)$, мы хотим выяснить, для каких $m$ условие
@ax:reciprocity-local-filtration выполняется и что собой представляет группа
$C_infinity$. На последний вопрос ответ весьма прост:
_$C_infinity$ совпадает со всей группой $mu_m$, кроме того случая, когда каждое
нормирование $v in S_infinity$ комплексное._

Далее, предложение (A.17) (см. также (3.1)) из работы Басса, Милнора, Серра
@bib:Bass1967a утверждает, что условие @ax:reciprocity-local-filtration
выполняется #source(265)в точности тогда, когда
$ frac(v_frak(p) (frak(q)), v_frak(p) (p)) - frac(1, p - 1) >= v_p (m), $
где $p = char(frac(A, frak(p)))$. На этом пути можно получить с помощью
предложения @prop:number-field-symbol-reciprocity некоторые
$frak(q)$-взаимности. Одна из основных теорем (см.
@th:bass-milnor-serre-reciprocity ниже) утверждает, что других не существует.
Приведем здесь эту теорему, чтобы иметь возможность ссылаться на нее в
дальнейшем.

#theorem(title: [Басс, Милнор, Серр])[
  Пусть $A$ — дедекиндово кольцо, поле частных $L$ которого является конечным
  расширением поля $QQ$. Тогда:
  #condition-list[
    #condition-item(format: "cyrillic")[Если поле $L$ не является вполне мнимым
      (т.~е. не существует $r$, для которого $RR tensor_QQ L tilde.eq CC^r$) или
      если $A$ не является кольцом целых алгебраических чисел в $L$, то
      $SK_1 (A, frak(q)) = 0$ для всех идеалов $frak(q)$ в $A$. Следовательно,
      не существует нетривиальных $frak(q)$-взаимностей.]
    <cond:bass-milnor-serre-triviality>
    #condition-item(format: "cyrillic")[Допустим, что поле $L$ вполне мнимое,
      $A$ — его кольцо алгебраических чисел. Через $m$ обозначим число корней из
      единицы в поле $L$. Пусть $frak(q) != 0$ — идеал кольца $A$. Для любого
      простого делителя $p$ числа $m$ через $j_p$ обозначим целое число из
      интервала $[0, v_p (m)]$, ближайшее к числу
      $
        min_(frak(p) divides p A)
        floor(frac(v_frak(p) (frak(q)), v_frak(p) (p)) - frac(1, p - 1)),
      $
      <eq:bass-milnor-serre-root-exponent>
      где $floor(x)$ означает целую часть числа $x$ для $x in RR$. Тогда
      $ SK_1 (A, frak(q)) tilde.eq mu_r quad ("r-е корни из единицы"), $
      где
      $ r = r(frak(q)) = product_(p divides m) p^(j_p). $
      В силу @prop:number-field-symbol-reciprocity $r$-й степенной закон
      взаимности в $L$ индуцирует универсальную $frak(q)$-взаимность. Если
      $0 != frak(q)' subset frak(q)$ и $r' = r(frak(q)')$, то естественный
      гомоморфизм $SK_1 (A, frak(q)') -> SK_1 (A, frak(q))$ соответствует
      $(r' / r)$-му степенному отображению $mu_(r') -> mu_r$ $(subset mu_(r'))$.
    ] <cond:bass-milnor-serre-imaginary-roots>
  ]
] <th:bass-milnor-serre-reciprocity>
#idx("теорема", "Басса — Милнора — Серра")

Из приведенной выше формулы @eq:bass-milnor-serre-root-exponent легко следует,
что $j_p = 0$, если $v_frak(p) (frak(q)) <= v_frak(p) (p)$ для некоторого
простого делителя $frak(p)$ элемента $p$. С другой стороны, например, если
$p^(2 v_p (m))$ делит $frak(q)$, то $j_p = v_p (m)$. Таким образом, в случае
@cond:bass-milnor-serre-imaginary-roots:

#numbered-formula-item[Группа $SK_1 (A, frak(q))$ не имеет $p$-кручения, если
  $v_frak(p) (frak(q)) <= v_frak(p) (p)$ для некоторого $frak(p)$, делящего
  $p$.] <eq:bass-milnor-serre-no-p-torsion>

#numbered-formula-item[Если $p^(2 v_p (m))$ делит $frak(q)$ (например, если
  $m^2$ делит $frak(q)$), то $p$-примарная часть группы $SK_1 (A, frak(q))$
  изоморфна $p$-примарной части группы
  $mu_m$.] <eq:bass-milnor-serre-full-p-torsion>

#source(266)
#corollary[
  Пусть кольцо $A$ удовлетворяет условиям теоремы
  @th:bass-milnor-serre-reciprocity. Тогда $SK_1 (A) = 0$ и для всех $n >= 3$
  справедливо равенство $SL_n (A) = E_n (A)$#footnote[
    Кон @bib:Cohn1966 доказал, что $SL_2 (A) != E_2 (A)$, если $A$ — неевклидово
    кольцо целых алгебраических чисел в мнимом квадратичном расширении поля
    рациональных чисел. Во всех остальных случаях $SL_2 (A) = E_2 (A)$
    (Васерштейн @bib:Vaserstein1972). — _Прим. ред._
  ], причем это — конечно порожденная группа.
] <cor:arithmetic-special-linear-elementary>
#name-idx("Васерштейн Л. Н.")

Обращение в нуль группы $SK_1 (A)$, даже в случае
@cond:bass-milnor-serre-imaginary-roots, следует из
@th:bass-milnor-serre-reciprocity и приведенного выше утверждения
@eq:bass-milnor-serre-no-p-torsion. Оставшиеся утверждения вытекают из
@cor:linear-stability-dimension-bound и @cor:elementary-group-finite-generation.

Заметим, что теорему @th:bass-milnor-serre-reciprocity можно также использовать
вместе с теоремой @th:linear-normal-subgroup-stability для определения
нормальных делителей группы $SL_n (A)$ при $n >= 3$. В свою очередь это дает
решение «конгруэнц-проблемы» для $SL_n (A)$, т.~е. вопроса о существовании
подгруппы конечного индекса в группе $SL_n (A)$, не содержащей
конгруэнц-подгруппы. Последнее случается в точности тогда, когда $A$ является
кольцом целых величин некоторого вполне мнимого числового поля.
