#import "main-defs.typ": (
  K, SK, U, det, ed-note, maxSpec, mennicke, res, source, tensor,
)
#import "statements.typ": condition-item, condition-list
#import "diagrams/reciprocity-finiteness-functoriality.typ": (
  reciprocity-categories, reciprocity-k-groups,
)

== Функториальные свойства законов взаимности <sec:reciprocity-functoriality>

Как и в предыдущем параграфе, зафиксируем дедекиндово кольцо $A$ с полем частных
$L=S^(-1)A$, где $S=A without {0}$, и ненулевым идеалом $frak(q)$.

Из @prop:dedekind-torsion-mennicke-surjection получаем эпиморфизм
$
  chi(frak(q)):product.co_(frak(p) divides.not frak(q)) U(A slash frak(p))
  -> SK_1 (A,frak(q)),
$
индуцированный вложением
$bold(italic(M))_S (A,frak(q)) subset bold(italic(M))(A,frak(q))$. Здесь мы
отождествили $U(A slash frak(p))$ с
$K_1 (A slash frak(p))=K_1 (bold(italic(M))(A slash frak(p)))$. Кроме того,
#source(539)если
$ chi_frak(p) (frak(q)):U(A slash frak(p)) -> SK_1 (A,frak(q)) $
является $frak(p)$-компонентой эпиморфизма $chi(frak(q))$, то опять же в силу
@prop:dedekind-torsion-mennicke-surjection получаем
$
  chi_frak(p) (frak(q))(u)=mennicke(frak(p) frak(q), a)
  quad (a equiv 1 mod frak(q),a equiv u mod frak(p)).
$

Пусть $A'$ — целое замыкание кольца $A$ в конечном расширении $L'$ поля $L$.
Таким образом, $L'=(S')^(-1)A'$, где $S'=A' without {0}$. Далее, пусть
$frak(q)'$ — идеал кольца $A'$, содержащий идеал $frak(q)$. Тогда мы получаем
коммутативную диаграмму точных функторов
$ #reciprocity-categories() $
индуцированную вложением $f:A -> A'$. Она в свою очередь индуцирует
коммутативную диаграмму
$ #reciprocity-k-groups() $
Для вычисления отображения $f_*$, соответствующего нижней стрелке, пусть элемент
$u in U(A slash frak(p))$ отождествляется с
$[A slash frak(p),u]_S in K_1 (bold(italic(M))_S (A,frak(q)))$. Тогда
$
  f_*(u)=f_*[A slash frak(p),u]
  =[(A slash frak(p)) tensor_A A',u tensor 1_(A')]_(S')
  =[A' slash (frak(p) A'),u]_(S').
$
Пусть $frak(p) A'=product (frak(p)')^(e_(frak(p)' slash frak(p)))$ — разложение
на простые множители идеала $frak(p) A'$. Тогда $A' slash (frak(p) A')=product
(A' slash (frak(p)')^(e_(frak(p)' slash frak(p))))$, при этом каждый из модулей
$A' slash (frak(p)')^e$ обладает рядом Жордана — Гёльдера длины $e$ с факторами
$A' slash frak(p)'$. Следовательно,
$
  f_*[A slash frak(p),u]=sum_(frak(p)' divides frak(p))
  e_(frak(p)' slash frak(p)) [A' slash frak(p)',u]
  =sum_(frak(p)' divides frak(p))
  [A' slash frak(p)',u^(e_(frak(p)' slash frak(p)))].
$

#source(540)Таким образом, $f_*$ как гомоморфизм из
$product.co_(frak(p) divides.not frak(q)) U(A slash frak(p))$ в
$product.co_(frak(p)' divides.not frak(q)') U(A' slash frak(p)')$
индуцирован гомоморфизмами
$
  f_(*frak(p)):U(A slash frak(p)) ->
  product.co_(frak(p)' divides frak(p)) U(A' slash frak(p)'),
$
$
  f_(*frak(p)) (u)=(u^(e_(frak(p)' slash frak(p))))_(frak(p)' divides frak(p)).
$
Переходя к соответствующим символам Меннике, получим
$
  f_* mennicke(frak(p) frak(q), a)=
  product_(frak(p)' divides frak(p))
  mennicke(frak(p)' frak(q)', a)^(e_(frak(p)' slash frak(p)))
  =mennicke(frak(p) A' frak(q)', a)=mennicke(frak(p) frak(q)', a).
$

Предположим теперь, что $frak(q)'=frak(q) A'$ и $A'$ конечен как $A$-модуль.
Тогда функтор ограничения $bold(italic(M))(A') -> bold(italic(M))(A)$ индуцирует
коммутативную диаграмму точных функторов
$ #reciprocity-categories(restriction: true) $
И снова мы получаем индуцированные гомоморфизмы
$ #reciprocity-k-groups(restriction: true) $
Если $u' in U(A' slash frak(p)')$, то элемент $u'$ отождествляется с элементом
$[A' slash frak(p)',u']_(S')$ группы $K_1 (bold(italic(M))_(S') (A',frak(q)'))$
и
$ f^*(u')=f^*[A' slash frak(p)',u']_(S')=[A' slash frak(p)',u']_S. $
В дальнейшем мы будем рассматривать $A' slash frak(p)'$ как $A$-модуль, а
умножение на $u'$ как $A$-автоморфизм. Если $frak(p)=A inter frak(p)'$, то
$A' slash frak(p)'$ — векторное пространство над $A slash frak(p)$, а класс в
группе $K_1 (A slash frak(p))$ элемента $[A' slash frak(p)',u']_S$ в точности
равен $(A slash frak(p))$-определителю автоморфизма
$u' dot 1_(A' slash frak(p)')$. В силу определения — это норма элемента $u'$:
$ [A' slash frak(p)',u']_S=[A slash frak(p),N_(frak(p)' slash frak(p)) u']_S, $
#source(541)где $N_(frak(p)' slash frak(p))$ обозначает отображение нормы из
$A' slash frak(p)'$ в $A slash frak(p)$. Таким образом, гомоморфизм
$
  f^*:product.co_(frak(p)' divides.not frak(q)') U(A' slash frak(p)') ->
  product.co_(frak(p) divides.not frak(q)) U(A slash frak(p))
$
индуцирован норменными гомоморфизмами
$
  f_(frak(p)')^*=N_(frak(p)' slash frak(p)):U(A' slash frak(p)') ->
  U(A slash frak(p)) quad (frak(p)' inter A=frak(p)).
$
Переходя к соответствующим символам Меннике, получим следующую формулу.
_Пусть $a' in A'$ представляет $u' in U(A' slash frak(p)')$. Выберем
$a' equiv 1 mod frak(q)'$. Тогда из приведенных выше равенств следует, что_
$ f^* mennicke(frak(p)' frak(q)', a')=mennicke(frak(p) frak(q), a), $
_где $a in A$ представляет $N_(frak(p)' slash frak(p)) u'$ и
$a equiv 1 mod frak(q)$._ Пусть $L_frak(p)$ есть $frak(p)$-адическое пополнение
поля $L$, а $L'_(frak(p)')$ есть $frak(p)'$-адическое пополнение поля $L'$. Из
основных результатов теории нормирований следует, что
$
  N_(L'_(frak(p)') slash L_frak(p)) (a') equiv
  (N_(frak(p)' slash frak(p)) (u'))^(e_(frak(p)' slash frak(p))) mod frak(p).
$
Таким образом,
$N_(L'_(frak(p)') slash L_frak(p)) (a') equiv
a^(e_(frak(p)' slash frak(p))) mod frak(p)$
и, следовательно,
$
  f^* mennicke(frak(p)' frak(q)', a')^(e_(frak(p)' slash frak(p)))
  =mennicke(frak(p) frak(q), N_(L'_(frak(p)') slash L_frak(p)) (a')).
$ <eq:reciprocity-local-norm-transfer>
#ed-note[
  В правом символе локальная норма означает её вычет по $frak(p)$: нижним
  аргументом служит представитель этого вычета в $A$, сравнимый с $1$ по
  $frak(q)$. Он существует по китайской теореме об остатках, а значение символа
  не зависит от выбора представителя в силу
  @prop:dedekind-torsion-mennicke-surjection.
]
Так как
$
  N_(L' slash L) (a')=product_(frak(p)' divides frak(p))
  N_(L'_(frak(p)') slash L_frak(p)) (a'),
$
то можно рассмотреть произведение равенств @eq:reciprocity-local-norm-transfer
по $frak(p)'$, делящим $frak(p)$, и получить равенство
$
  mennicke(frak(p) frak(q), N_(L' slash L) (a'))=
  product_(frak(p)' divides frak(p)) f^*
  mennicke(frak(p)' frak(q)', a')^(e_(frak(p)' slash frak(p)))
  =f^* mennicke(frak(p) frak(q)', a').
$
Так как обе части равенства мультипликативны по всем переменным, то
$
  mennicke(frak(b) frak(q), N_(L' slash L) (a'))
  =f^* mennicke(frak(b) frak(q)', a'),
$
<eq:reciprocity-global-norm-transfer>
как только $a' equiv 1 mod frak(q)'$ и идеал $frak(b) subset A$ взаимно прост с
$a'$.

Мы закончим этот параграф разбором примера, принадлежащего Милнору. Пусть
$A=RR[x,y]$, где $x^2+y^2=1$ (т.~е. вещественное #source(542)координатное кольцо
окружности $S^1 subset RR^2$). Тогда мы утверждаем, что
$ SK_1 (A) approx ZZ slash (2 ZZ). $
Отождествим $S^1$ с подмножеством пространства $maxSpec(A)$.

#condition-list[
  #condition-item(format: "step")[_Экспонента группы $SK_1 (A)$ равна $2$._
    Действительно, $CC tensor_(RR) A=CC[u,u^(-1)]$, где $u=x+y sqrt(-1)$ и
    $u^(-1)=x-y sqrt(-1)$. Так как это — локализация евклидова кольца $CC[u]$,
    то $SK_1 (CC tensor_(RR) A)=0$. Композиция отображений
    $SK_1 (A) -> SK_1 (CC tensor_(RR) A) arrow.r^res SK_1 (A)$ совпадает с
    умножением на элемент $[CC]_(RR)=2 in K_0 (RR)$ (см.
    @prop:projective-k-transfer-scalar-multiplication). Это доказывает первое
    утверждение.]
  <cond:circle-sk1-exponent-two>

  #condition-item(format: "step")[_Пусть $frak(p) in maxSpec(A)$ и
    $a in.not frak(p)$. Пусть $[ ]$ — символ Меннике. Тогда
    $mennicke(frak(p), a)=1$, если $frak(p) in.not S^1$. Если же
    $frak(p) in S^1$, то $mennicke(frak(p), a)$ зависит лишь от знака
    $a(frak(p))$_ (т.~е. от образа элемента $a$ в $A slash frak(p) approx RR$).
    Действительно, у группы $U(CC)$ нет нетривиальных факторгрупп экспоненты
    два. Единственная такая факторгруппа группы $U(RR)$ соответствует
    гомоморфизму, связанному со знаком. Так как отображение
    $a mapsto mennicke(frak(p), a)$ индуцирует гомоморфизм на
    $U(A slash frak(p))$, то требуемое утверждение следует из шага
    @cond:circle-sk1-exponent-two.]
  <cond:circle-sk1-symbol-sign>

  #condition-item(format: "step")[_Пусть $[ ]$ — универсальный символ Меннике со
    значениями в группе $SK_1 (A)$. Тогда группа $SK_1 (A)$ порождается
    элементами вида $e_frak(p)=mennicke(frak(p), -1)$ ($frak(p) in S^1$)._
    Это непосредственно следует из результата, полученного на шаге
    @cond:circle-sk1-symbol-sign.] <cond:circle-sk1-sign-generators>

  #condition-item(format: "step")[_Если $frak(p)_1,frak(p)_2 in S^1$, то идеал
    $frak(p)_1 frak(p)_2$ главный и, следовательно,
    $e_(frak(p)_1)=e_(frak(p)_2)$._

    Пусть элемент $d=a x+b y-c in A$, где $a,b,c in RR$, выбран так, что прямая
    $a x+b y=c$ в $RR^2$ проходит через $frak(p)_1$ и $frak(p)_2$ и касательна к
    $S^1$, если $frak(p)_1=frak(p)_2$. Тогда функция $d$ имеет нуль первого
    порядка в каждом из идеалов $frak(p)_i$, если $frak(p)_1!=frak(p)_2$, и нуль
    порядка два в $frak(p)_1$, если $frak(p)_1=frak(p)_2$. Ясно, что других
    нулей у $d$ на окружности $x^2+y^2=1$ в $CC^2$ нет. Поэтому
    $frak(p)_1 frak(p)_2=d A$. Теперь получаем
    $
      e_(frak(p)_1) e_(frak(p)_2)=
      mennicke(frak(p)_1, -1) mennicke(frak(p)_2, -1)
      =mennicke(frak(p)_1 frak(p)_2, -1)=mennicke(d, -1)=1.
    $
  ] <cond:circle-sk1-equal-generators>
]

Результаты, полученные на шагах
@cond:circle-sk1-exponent-two–@cond:circle-sk1-equal-generators, показывают, что
порядок группы $SK_1 (A)$ не превосходит двух. Доказательство будет закончено,
как только мы покажем, что группа $SK_1 (A)$ нетривиальна. Но это следует из
явной формы закона взаимности, построенного в конце гл.~@ch:mennicke-symbols,
§~@sec:curve-reciprocity.
