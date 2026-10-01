#import "main-defs.typ": (
  Coker, End, Im, Ker, det, idx, moduleCategoryOf, source, tensor,
)
#import "statements.typ": condition-item, condition-list, proof, proposition
#import "diagrams/polynomial-fundamental-theorem-characteristic.typ": (
  characteristic-sequence,
)

== Характеристическая последовательность для эндоморфизма
<sec:endomorphism-characteristic-sequence>

В этом параграфе $t$ обозначает переменную. Если $A$ — кольцо и если
$M in moduleCategoryOf(A)$, то отождествим $M tensor_A A[t]$ с
$ M[t] = {sum_(i >= 0) m_i t^i | m_i in M, m_i = 0 "почти для всех" i}. $
Если $f: M -> N$ — гомоморфизм $A$-модулей, то
$ f[t]: M[t] -> N[t], quad f[t](sum m_i t^i) = sum f(m_i)t^i $
является $A[t]$-гомоморфизмом, соответствующим гомоморфизму $f tensor_A A[t]$.
Так как $A[t]$ — свободный $A$-модуль, то функтор $M mapsto M[t]$ точный.

Если $M in moduleCategoryOf(A[t])$, то $M$ полностью определяется как
$A[t]$-модуль:
#condition-list[
  #condition-item(format: "1)")[структурой $A$-модуля на $M$;]
  <cond:polynomial-module-underlying-module>
  #condition-item(format: "1)")[заданием $A$-эндоморфизма $f: M -> M$,
    $f(m) = m t$.]
  <cond:polynomial-module-variable-action>
]
При этом данные @cond:polynomial-module-underlying-module и
@cond:polynomial-module-variable-action можно задавать произвольным образом.
Итак, если $M in moduleCategoryOf(A)$ и $f in End_A (M)$, то определим
$A[t]$-модуль
$ M_f $
как аддитивную группу $M$ с $A[t]$-операцией $m(sum a_i t^i) = sum f^i (m)a_i$.
Таким образом мы устанавливаем изоморфизм категории $moduleCategoryOf(A[t])$ и
категории эндоморфизмов объектов категории $moduleCategoryOf(A)$.

Если нам даны $M in moduleCategoryOf(A)$ и $f in End_A (M)$, то рассмотрим
канонический $A[t]$-эпиморфизм
$ phi_f: M[t] -> M_f, quad phi_f (sum m_i t^i) = sum f^i (m_i). $
_Характеристической последовательностью_#idx(
  "характеристическая последовательность",
) для эндоморфизма $f$ называется точная последовательность
@eq:endomorphism-characteristic-sequence, приводимая ниже.

#proposition[
  Пусть $M in moduleCategoryOf(A)$ и $f in End_A (M)$. Тогда последовательность
  $ #characteristic-sequence() $
  <eq:endomorphism-characteristic-sequence>
  #source(481)точна в категории $moduleCategoryOf(A[t])$. Кроме того,
  отображение $(M, f) mapsto$ @eq:endomorphism-characteristic-sequence
  определяет точный функтор из категории эндоморфизмов $A$-модулей (которую мы
  можем отождествить с категорией $moduleCategoryOf(A[t])$) в категорию коротких
  точных последовательностей в категории $moduleCategoryOf(A[t])$.
] <prop:endomorphism-characteristic-sequence>

#proof[
  Ясно, что имеет место функториальная зависимость последовательности
  @eq:endomorphism-characteristic-sequence от $(M, f)$. Этот функтор, очевидно,
  точен, поскольку функторы $(M, f) mapsto M_f$ и $(M, f) mapsto M[t]$ точные.
  Остаётся показать, что последовательность
  @eq:endomorphism-characteristic-sequence точна. Как мы видели, отображение
  $phi_f$ сюръективно. Кроме того,
  $
    phi_f (t dot 1_(M[t]) - f[t])(sum m_i t^i)
    = phi_f (sum (m_i t^(i+1) - f(m_i)t^i))
    = sum (f^(i+1) (m_i) - f^i (f(m_i))) = 0.
  $
  Так как отображение $t dot 1_(M[t]) - f[t]$ повышает степень на единицу и
  сохраняет «старший коэффициент», то это отображение — мономорфизм.
  Предположим, наконец, что $x = sum m_i t^i in Ker (phi_f)$, т.~е. что
  $sum f^i (m_i) = 0$. Тогда
  $
    x = x - sum_(i >= 0) f^i (m_i)
    = sum_(i > 0) (m_i t^i - f^i (m_i))
    = sum_(i > 0) (t^i 1_(M[t]) - f^i)(m_i)
    = (t dot 1_(M[t]) - f[t]) sum_(i > 0) h_i (m_i)
    in Im (t dot 1_(M[t]) - f[t]),
  $
  где
  $ h_i = sum_(0 <= j < i) t^j 1_(M[t]) f^(i-j-1)[t]. $
]

_Замечание._ Предположим, что к тому же кольцо $A$ коммутативно и $M$ —
свободный $A$-модуль с базисом $e_1, dots, e_n$. Тогда $M[t]$ является свободным
$A[t]$-модулем с тем же самым базисом, а матрица преобразования $f[t]$ совпадает
с матрицей преобразования $f$. Таким образом, многочлен
$ P_f (t) = det (t dot 1_(M[t]) - f[t]) $
является _характеристическим многочленом_ преобразования $f$. Но (см.
@prop:determinant-divisor-characteristic @cond:determinant-annihilates-cokernel)
в случае коммутативного кольца, если $g: B^n -> B^n$ — гомоморфизм $B$-модулей,
то $Coker (g) dot det (g) = 0$. Применяя это замечание к характеристической
последовательности эндоморфизма $f$, мы видим, что многочлен $P_f (t)$
аннулирует модуль $M_f$. Однако эндоморфизм модуля $M_f$, определяемый
многочленом $P_f (t)$, совпадает в точности с $P_f (f)$. Таким образом, получаем
_теорему Гамильтона — Кэли_#idx("теорема Гамильтона — Кэли") $P_f (f) = 0$.
