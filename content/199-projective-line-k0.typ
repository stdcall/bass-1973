#import "main-defs.typ": *
#import "statements.typ": *
#import "diagrams/polynomial-fundamental-theorem-projective-line.typ": (
  projective-line-category-cospan, projective-line-category-square,
  projective-line-ring-square,
)

== Группа $K_0$ проективной прямой над $A$ <sec:projective-line-k0>

Мы собираемся изучить группу $K_0 (P^1 (A))$, где $P^1 (A)$ — «проективная
прямая» над $A$. Эта группа определяется следующим образом:
#symbol-idx($P^1 (A)$, sort: "P^1(A)", group: "groups", order: 114)
$ K_i (P^1 (A)) = K_i (bold(P)(P^1 (A))) quad (i=0,1), $
где $bold(P)(P^1 (A))$ — категория «алгебраических векторных расслоений над
$P^1 (A)$». Мы не будем определять ни одного из этих терминов, а лучше
непосредственно определим категорию $bold(P)(P^1 (A))$. Этого будет достаточно
для наших целей.

#source(516)Пусть, как и в предыдущем параграфе, $T$ — бесконечная циклическая
группа с образующим $t$, $T_±$ — подполугруппы, порожденные соответственно
элементами $t^(±1)$. Для любого кольца $A$ диаграмма
#projective-line-ring-square()
является декартовым квадратом (поскольку $A=A[T_+] inter A[T_-]$). Однако, так
как ни $tau_+$, ни $tau_-$ не являются сюръективными отображениями, то мы не
можем получить последовательности Майера — Вьеториса, в которую входят группы
$K_i (A)$. Тем не менее мы можем рассмотреть расслоенное произведение категорий
#projective-line-category-cospan()
и именно это расслоенное произведение обозначим через $bold(P)(P^1 (A))$. Таким
образом, получаем декартов квадрат
#numbered-condition[#projective-line-category-square()]
<eq:projective-line-category-square>
из функторов категорий с произведением $plus.o$ в смысле (@ch:exact-k-sequences,
§~@sec:fiber-product-categories). Напомним, что объектами категории
$bold(P)(P^1 (A))$ являются тройки $(P_+,alpha,P_-)$, где
$P_± in bold(P)(A[T_±])$ и $alpha: tau_+ P_+ -> tau_- P_-$ есть
$A[T]$-изоморфизм. Здесь мы пишем $tau_± P_± = P_± tensor_(A[T_±]) A[T]$.
Морфизм $(P_+,alpha,P_-) -> (Q_+,beta,Q_-)$ — это пара морфизмов
$f_±: P_± -> Q_±$, для которых $(tau_- f_-) alpha = beta (tau_+ f_+)$. Функторы
$g_±$ являются в точности левой и правой координатной проекциями.

Как легко видеть, функторы $(tau_+,tau_-)$ образуют «кофинальную пару» в смысле
@def:cofinal-functor-pair. Следовательно, можно применить
@th:mayer-vietoris-exact-sequence к диаграмме
@eq:projective-line-category-square и получить последовательность Майера —
Вьеториса #numbered-condition[
  $
    K_1 (P^1 (A)) arrow.r^(G_1) K_1 (A[T_+]) plus.o K_1 (A[T_-])
    arrow.r^(tau_1) K_1 (A[T]) arrow.r^(delta) K'_0 (P^1 (A))
    arrow.r^(G_0) K_0 (A[T_+]) plus.o K_0 (A[T_-]) arrow.r^(tau_0) K_0 (A[T]).
  $
] <eq:projective-line-mayer-vietoris>
Здесь мы положили $G_i = vec(g_+, -g_-)$ и $tau_i=(tau_+,tau_-)$. В силу
@th:mayer-vietoris-exact-sequence последовательность точна всюду, кроме,
возможно, члена $K_1 (A[T_+]) plus.o K_1 (A[T_-])$. Заметим, далее, что в
последовательность входит группа $K'_0 (P^1 (A))$, а не группа $K_0 (P^1 (A))$.
Первая #source(517)из них есть факторгруппа последней, определенная в
(@ch:exact-k-sequences, §~@sec:mayer-vietoris-sequence). Вскоре мы обсудим
различие между этими двумя группами.

В силу основной теоремы @th:fundamental-k-theory-laurent функтор $K_1$ стягиваем
и $K_0=L K_1$. Поэтому получаем канонические изоморфизмы:
#numbered-condition[$ Ker (tau_1) = K_1 (A); $]
<eq:projective-line-k-one-kernel>
#numbered-condition[$ Coker (tau_1) = L K_1 (A) approx K_0 (A); $]
<eq:projective-line-k-one-cokernel>
#numbered-condition[$ Ker (tau_0) = K_0 (A). $]
<eq:projective-line-k-zero-kernel>
Если $alpha in GL_n (A)$, то элемент $([alpha],-[alpha]) in Ker (tau_1)$
$(approx K_1 (A))$ является образом при $G_1$ элемента
$[(A^n [T_+],1_(A^n [T]),A^n [T_-]),(alpha[T_+],alpha[T_-])]
in K_1 (P^1 (A))$. Это показывает, что последовательность
@eq:projective-line-mayer-vietoris точна даже там, где это не утверждалось
теоремой @th:mayer-vietoris-exact-sequence.

Использовав @eq:projective-line-k-one-kernel, применим теперь изоморфизмы
@eq:projective-line-k-one-cokernel и @eq:projective-line-k-zero-kernel для
получения короткой точной последовательности: #numbered-condition[
  $ 0 -> K_0 (A) arrow.r^(d) K'_0 (P^1 (A)) arrow.r^(e) K_0 (A) -> 0, $
] <eq:projective-line-split-k-zero>
где $d$ индуцировано отображением $delta$ (с помощью
@eq:projective-line-k-one-cokernel), а $e$ индуцировано функтором $G_0$ (с
помощью @eq:projective-line-k-zero-kernel).

Теперь удобно ввести аддитивные функторы
$
  h^n: bold(P)(A) -> bold(P)(P^1 (A)),
  quad h^n (P) = (P[T_+],t^n dot 1_(P[T]),P[T_-])
$
и соответствующие гомоморфизмы
$ h^n: K_0 (A) -> K'_0 (P^1 (A)), quad h^n [P] = [h^n (P)]'. $
Гомоморфизм $e$ в последовательности @eq:projective-line-split-k-zero определен
так:
$ e[P_+,alpha,P_-]' = [P'_+] = [P'_-] in K_0 (A), $
где $P'_± in bold(P)(A)$ задается следующим образом:
$P'_±=P_± tensor_(A[T_±]) A$; при этом тензорное произведение рассматривается
относительно пополнения. Это вытекает из
@cor:contracted-k-zero-abelian-extensions. Таким образом, убеждаемся в том, что
гомоморфизм $e$ расщепляется каждым отображением $h^n$. Поэтому $h^n$ —
мономорфизмы, и
$ K'_0 (P^1 (A)) = Im (h^0) plus.o Im (d), $
причем каждое прямое слагаемое изоморфно группе $K_0 (A)$.

Чтобы описать $d$, достаточно, как показывает разложение группы $K_1 (A[T])$ в
@th:fundamental-k-theory-laurent, рассмотреть действие $delta$ (из
последовательности Майера — Вьеториса @eq:projective-line-mayer-vietoris) на
$K_0 (A)$-члене $Im (h_(T,A)) subset K_1 (A[T])$. Напомним, что гомоморфизм
$h=h_(T,A): K_0 (A) -> K_1 (A[T])$ определен так: $h[P]=[P[T],t dot 1_(P[T])]$
для $P in bold(P)(A)$. Из @th:mayer-vietoris-exact-sequence (где мы писали
$partial$ вместо $delta$) следует, что
$
  delta[P[T],t dot 1_(P[T])] = [P[T_+],t dot 1_(P[T]),P[T_-]]'
  - [P[T_+],1_(P[T]),P[T_-]]' = h^1 [P]-h^0 [P].
$

#source(518)Итак, $d=h^1-h^0$, и мы получаем
#numbered-condition[$ K'_0 (P^1 (A)) = h^0 K_0 (A) plus.o h^1 K_0 (A). $]
<eq:projective-line-k-zero-decomposition>
В группе $K_1 (A[T])$ справедливо равенство
$[P[T],t^2 1_(P[T])] = 2[P[T],t 1_(P[T])]$ для $P in bold(P)(A)$. Но вычисления,
аналогичные приведенным выше, показывают, что
$delta[P[T],t^2 1_(P[T])] = h^2 [P]-h^0 [P]$. Таким образом,
$h^2-h^0=2(h^1-h^0)$, т. е.
#numbered-condition[$ h^2-2h^1+h^0=0. $]
<eq:projective-line-h-second-difference>
Если определить формально произведение на $brace.l h^n brace.r$, полагая
$h^n h^m=h^(n+m)$, то можно записать равенство
@eq:projective-line-h-second-difference так:
#numbered-condition[$ (h^1-h^0)^2=0. $]
<eq:projective-line-h-square-zero>
Если элементы $h^n K_0 (A)$ порождают группу $K'_0 (P^1 (A))$, то соотношение
@eq:projective-line-h-second-difference и его «переносы»
$h^(n+1)-2h^n+h^(n-1)=0$ $(n in ZZ)$ уже определяют разложение
@eq:projective-line-k-zero-decomposition. Таким образом, соотношение
@eq:projective-line-h-second-difference и его «переносы» задают полную систему
соотношений между $h^n$. Тем самым установлена

#theorem[
  Пусть $A$ — кольцо. Определим
  #symbol-idx($h^n$, sort: "h^n", group: "groups", order: 105)
  $ h^n: K_0 (A) -> K'_0 (P^1 (A)) quad (n in ZZ), $
  полагая $h^n [P] = [P[T_+],t^n dot 1_(P[T]),P[T_-]]'$. Тогда $h^n$ являются
  мономорфизмами, а полная система аддитивных соотношений между ними такова:
  $ h^(n+1)-2h^n+h^(n-1)=0 quad (n in ZZ). $
  Кроме того,
  $ K'_0 (P^1 (A)) = h^0 K_0 (A) plus.o h^1 K_0 (A). $
] <th:projective-line-k-zero>

Замечания: 1) Отметим, что в последнюю формулу входит группа $K'_0$, а не $K_0$.
Напомним (@ch:exact-k-sequences, §~@sec:mayer-vietoris-sequence), что
$ K'_0 (P^1 (A)) = frac(K_0 (P^1 (A)), M), $
где подгруппа $M$ группы $K_0 (P^1 (A))$ порождается элементами следующего типа.
Пусть $P=(P_+,alpha,P_-) in bold(P)(P^1 (A))$ и
$alpha_1,alpha_2 in Aut_(A[T]) (tau_+ P_+)$. Записывая
$P alpha_1=(P_+,alpha alpha_1,P_-) in bold(P)(P^1 (A))$, положим
$
  chevron.l P,alpha_1,alpha_2 chevron.r = [P alpha_1 alpha_2]+[P]
  - ([P alpha_1]+[P alpha_2]) in K_0 (P^1 (A)).
$
Эти элементы порождают $M$ ($P$ и $alpha_i$ — переменные). Критерий равенства
нулю группы $M$ приведен в @lem:mayer-vietoris-stable-relations. В нашем случае
он не выполняется, даже если $A$ — поле. Действительно, если $A$ — поле, то
теорема Крулля — Шмидта имеет место в категории $bold(P)(P^1 (A))$, а
следовательно, $K_0 (P^1 (A))$ — свободная абелева группа с базисом, состоящим
из классов неразложимых объектов. #source(519)Эти элементы имеют вид $h^n [A]$
$(n in ZZ)$. Поэтому $K_0 (P^1 (A))$ — свободная группа бесконечного ранга, хотя
ранг группы $K'_0 (P^1 (A))$ равен 2.#ed-note[
  Здесь следует различать группу, построенную только по отношениям прямой суммы,
  и современную $K_0$ точной категории векторных расслоений $bold(P)(P^1 (A))$.
  Для последней теорема о проективной прямой даёт
  $K_n (P^1 (A)) approx K_n (A) plus.o K_n (A)$ для любого кольца $A$ и
  $n >= 0$. Поэтому при поле её $K_0$ имеет ранг два; бесконечный ранг указанной
  в тексте группы относится к отношениям прямой суммы. См. Вайбель
  @bib:Weibel2013, гл.V, теорема 1.5.4.
]

2) Можно было бы надеяться обобщить утверждение о том, что если $A$ — поле, то
каждый объект категории $bold(P)(P^1 (A))$ является прямой суммой объектов вида
$h^n (A)$. Можно допустить, что для любого кольца $A$ каждый объект стабильно
равен прямой сумме объектов вида $h^n (P)$ $(n in ZZ,P in bold(P)(A))$. Это
означало бы, что каждый двойной смежный класс в
$GL(A[T_-]) backslash GL(A[T])/GL(A[T_+])$ представим элементом
$tau in GL_m (A[T])$ (для некоторого $m$) следующего типа: существуют разложение
$A^m=P_1 plus.o dots plus.o P_r$ и целые числа $n_1,dots,n_r$, такие, что
$ tau=t^(n_1) 1_(P_1 [T]) plus.o dots plus.o t^(n_r) 1_(P_r [T]) $
(т. е. матрица $tau$ «диагонализируема» над $A$, а ее собственные значения лежат
в $T$).

Допустим теперь, что кольцо $A$ коммутативно. Тогда можно рассмотреть
естественное тензорное произведение в категории $bold(P)(P^1 (A))$:
$
  (P_+,alpha,P_-) tensor (Q_+,beta,Q_-)
  = (P_+ tensor_(A[T_+]) Q_+,alpha tensor_(A[T]) beta,P_- tensor_(A[T_-]) Q_-).
$
Кроме того, функтор
$ h^0: bold(P)(A) -> bold(P)(P^1 (A)), $
введенный выше, сохраняет тензорные произведения, и
$ h^0 (A) tensor W approx W "для всех" W in bold(P)(P^1 (A)). $
Далее,
$ h^n (A) tensor h^m (P) approx h^(n+m) (P), $
$ h^n (P) approx h^n (A) tensor h^0 (P). quad (P in bold(P)(A)) $
Это показывает, что $K_0 (P^1 (A))$ является коммутативным кольцом, причем $h^0$
превращает его в $K_0 (A)$-алгебру. Подгруппа же, порожденная образами всех
$h^n: K_0 (A) -> K_0 (P^1 (A))$, в точности совпадает с подалгеброй, порожденной
над $K_0 (A)$ элементом
$ h=[h^1 (A)]. $
Я не смог установить аналог соотношения @eq:projective-line-h-second-difference:
$ (h-1)^2=0? $
Однако мы можем показать, что группа $K'_0 (P^1 (A))$ наследует структуру
алгебры, а тогда приведенное соотношение имеет смысл и справедливо в $K'_0$.
Требуется лишь показать, что определенная выше подгруппа
$M subset K_0 (P^1 (A))$ является идеалом.

#source(520)Пусть $chevron.l P,alpha_1,alpha_2 chevron.r$ — один из образующих
подгруппы $M$ и $Q=(Q_+,beta,Q_-) in bold(P)(P^1 (A))$. Надо показать, что
$chevron.l P,alpha_1,alpha_2 chevron.r [Q] in M$. Если
$gamma in Aut_(A[T]) (tau_+ P_+)$, то положим
$gamma'=gamma tensor_(A[T]) 1_(tau_+ Q_+)$. Тогда ясно, что
$ P gamma tensor Q=(P tensor Q)gamma', $
откуда следует, что
$
  chevron.l P,alpha_1,alpha_2 chevron.r [Q]
  = chevron.l P tensor Q,alpha'_1,alpha'_2 chevron.r.
$

Теперь можно переформулировать теорему @th:projective-line-k-zero для случая
коммутативного кольца следующим образом.

#corollary[
  Пусть $A$ — коммутативное кольцо. Тогда группа $K'_0 (P^1 (A))$ является
  коммутативной $K_0 (A)$-алгеброй (используем $h^0$). Как $K_0 (A)$-алгебра она
  задается одним образующим $h'=[h^1 [A]]'$ и одним соотношением
  $ (h'-1)^2=0. $
] <cor:projective-line-k-zero-algebra>
