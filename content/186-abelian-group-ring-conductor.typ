#import "main-defs.typ": (
  Aut, Coker, Gal, Gcd, H, Ker, Lcm, Nr, U, ann, card, char, idx, source,
  tensor,
)
#import "statements.typ": corollary, numbered-condition, proof, proposition
#import "diagrams/finite-group-induction-applications.typ": (
  conductor-projection-triangle, conductor-square,
)

== Кондуктор абелева группового кольца <sec:abelian-group-ring-conductor>

Если $R$ — кольцо целых величин числового поля, то из теорем
(гл.~@ch:arithmetic-finiteness, §~@sec:finiteness-of-class-number) следует, что
все группы, появляющиеся в следствии @cor:group-ring-cartan-kernel-comparison,
являются конечными. С помощью теорем индукции можно получить информацию об
экспонентах этих групп, как только мы узнаем их поведение для абелевой группы
$pi$ (или даже для циклической группы). Если группа $pi$ абелева, то целое
замыкание кольца $R pi$ является произведением колец алгебраических чисел.
Поэтому его арифметическое строение относительно прозрачно. Для проведения
тщательного сравнения кольца $R pi$ с его целым замыканием надо сначала
вычислить кондуктор. Это и является задачей этого параграфа.

Для начала пусть $A$ — коммутативное кольцо, в котором нулевой идеал является
несократимым пересечением минимальных простых идеалов:
$ (0)=frak(p)_1 inter dots inter frak(p)_n. $
Тогда $A_i=A slash frak(p)_i$ — область целостности $(1<=i<=n)$ и
$A subset B=product_i A_i$. Проекции $rho_i:A -> A_i$ индуцированы
покоординатными проекциями в произведении $B$. _Кондуктором_#idx("кондуктор") из
$B$ в $A$ называется множество
$ frak(c)=frak(c)_(B slash A)={a in A | a B subset A}. $
Кондуктор является наибольшим $B$-идеалом, содержащимся в $A$. Будучи
$B$-идеалом, кондуктор является прямой суммой своих компонент:
$
  frak(c)=union.sq.big_i frak(c)_i, quad
  frak(c)_i={a in frak(c) | rho_j (a)=0 "для всех" j!=i}.
$
<eq:conductor-component-decomposition>
Таким образом, $frak(c)_i subset inter_(j!=i) frak(p)_j
={a in A | rho_j (a)=0 "для всех" j!=i}$. Так как
$frak(p)_i (inter_(j!=i) frak(p)_j)=0$, то $frak(c)_i subset ann_A (frak(p)_i)$.
Но $ann_A (frak(p)_i)$ является моду#source(463)лем над кольцом
$A slash frak(p)_i$. Следовательно, это $B$-идеал, и поэтому он содержится в
$frak(c)$. Итак,
$ frak(c)_i=inter_(j!=i) frak(p)_j=ann_A (frak(p)_i)!=0. $
<eq:conductor-component-annihilator>

Пусть $I={1,dots,n}$. Если $J subset I$, то положим $B_J=product_(j in J) A_j$.
Если отображение $f=f_J:A -> B_J$ индуцировано проекцией $B -> B_J$, то положим
$A_J=Im (f)$ и $frak(a)=Ker (f)$. Допустим, что $ann_A (frak(a))=N dot A$ (где
правая часть — главный идеал, порожденный некоторым элементом $N in A$). Так как
в $ann_A (frak(a))$ лежат все $frak(c)_j$ $(j in J)$, то $f (N)$ не является
делителем нуля в $A_J$ (или даже в $B_J$; при этом мы использовали то, что
$frak(c)_j!=0$ для всех $j$). Покажем теперь, что #numbered-condition[
  для каждого $j in J$,
  $ann_A (frak(p)_j)=N dot f^(-1) (ann_(A_J) (f (frak(p)_j)))$, и поэтому
  $f (ann_A (frak(p)_j))=f (N) dot ann_(A_J) (f (frak(p)_j))$.
] <eq:conductor-annihilator-projection>
Действительно, так как $frak(a) subset frak(p)_j$, то
$ann_A (frak(a))=N dot A supset ann_A (frak(p)_j)$. Если
$a in ann_A (frak(p)_j)$, то положим $a=N b$. Применим $f$ к равенству
$N b frak(p)_j=0$. Как было замечено ранее, $f (N)$ не является делителем нуля.
Поэтому $f (b) in ann_(A_J) (f (frak(p)_j))$. Таким образом,
$ ann_A (frak(p)_j) subset N dot f^(-1) (ann_(A_J) (f (frak(p)_j))). $
Обратно предположим, что $b in A$ и $f (b) in ann_(A_J) (f (frak(p)_j))$. Тогда
$b frak(p)_j subset Ker (f)=frak(a)$. Таким образом, поскольку
$N dot A=ann_A (frak(a))$, мы имеем $N b frak(p)_j=0$, т. е.
$N b in ann_A (frak(p)_j)$. Второе равенство получается путем применения $f$ к
первому равенству.

Допустим далее, что $ann_(A_J) (f (frak(p)_j))=f (d) A_J$, т. е. является
главным идеалом. Тогда мы покажем, что для $j in J$: #numbered-condition[
  $frak(c)_j=N d A$ (если $ann_A (Ker (f_J))=N A$ и если
  $ann_(A_J) (f_J (frak(p)_j))=f_J (d) A_J$).
] <eq:conductor-principal-component>
Действительно, если $a in A$, то
$f (d a frak(p)_j)=f (a) f (d) f (frak(p)_j)=0$. Поэтому
$d a frak(p)_j subset Ker (f)=frak(a)$. Так как $N frak(a)=0$, то
$N d a frak(p)_j=0$. Итак, $N d a in ann_A (frak(p)_j)=frak(c)_j$. Обратно,
пусть $a frak(p)_j=0$. Тогда в силу @eq:conductor-annihilator-projection
$a=N b$, где $f (b) f (frak(p)_j)=0$. Следовательно, $f (b)=f (d) f (c)$ для
некоторого элемента $c$, т. е. $b-d c in Ker (f)=frak(a)$. Таким образом,
$a=N b=N d c$, поскольку $N frak(a)=0$. Это завершает доказательство.

Теперь применим эти замечания в следующей ситуации: #numbered-condition[
  $R$ — целозамкнутая область целостности;

  $L$ — поле частных кольца $R$, $char L=0$;

  $pi$ — конечная абелева группа порядка $m=[pi:1]$;

  $#source(464)L pi=product_(i in I) L_i$, где поля $L_i$ являются (конечными
  циклотомическими) расширениями поля $L$;

  $A=R pi$;

  $B=product_(i in I) A_i$, где $A_i$ — проекция кольца $A$ в поле $L_i$.
] <eq:abelian-group-ring-conductor-data>

Пусть $frak(p)_i=Ker (rho_i)$, где $rho_i:A -> A_i subset L_i$ — проекция. Тогда
идеалы $frak(p)_i$ простые и $inter_(i in I) frak(p)_i=(0)$, поскольку
$A subset L pi=product_(i in I) L_i$. Легко видеть, что это пересечение простых
идеалов несократимо, т. е. что $inter_(j in J) frak(p)_j!=0$ для всех
собственных подмножеств $J subset I$. Это следует, например, из того, что $A$
является $R$-решеткой в $L pi$. В равной степени можно было бы использовать
теорию примарных разложений (которая не рассматривалась).

Если $m>=1$, то через $mu_m$ обозначим группу корней $m$-й степени из единицы (в
алгебраическом замыкании любого рассматриваемого здесь поля). Тогда
$L_i=L [mu_(m_i)]$, где $mu_(m_i)=rho_i (pi)$. Определим ядро $pi_i$ следующей
точной последовательностью:
$ 1 -> pi_i -> pi arrow.r^(rho_i) mu_(m_i) -> 1. $
<eq:abelian-group-cyclotomic-quotient>
Так как $A=R pi$, то $A_i=rho_i (A)=R [mu_(m_i)]$.

Мы собираемся вычислить компоненты $frak(c)_i$ $(i in I)$ кондуктора
$frak(c)=frak(c)_(B slash A)$, используя описанный выше метод. Зафиксируем
$i in I$ и рассмотрим коммутативную диаграмму
$ #conductor-projection-triangle() $
Тогда во введенных выше обозначениях $A'=A_J$, где
$J={j | pi_i subset pi_j}={j | rho_j (pi_i)={1}}$. Идеал $frak(a)=Ker (f)$
порождается всеми элементами вида $1-x$ $(x in pi_i)$. Покажем, что
#numbered-condition[
  $ann_A (frak(a))=N_i A$, где $frak(a)=Ker (R pi -> R [pi slash pi_i])$ и
  $N_i=sum_(x in pi_i) x$.
] <eq:group-augmentation-annihilator>
Так как $A$ является свободным $R pi_i$-модулем и так как идеал $frak(a)$
порождается элементами из $R pi_i$, то достаточно доказать это для случая, когда
$pi=pi_i$. Ясно, что $x N_i=N_i$ для всех $x in pi_i$. Поэтому $N_i frak(a)=0$.
Обратно, если $a=sum a_x x$ $(x in pi_i)$ и $a dot frak(a)=0$, то $y a=a$
#source(465)для всех $y in pi_i$. Поэтому $a_x=a_(y x)$ для всех $x in pi_i$.
Таким образом, как и утверждалось, $a=a_1 dot N_i$.

Пусть $sigma_i=pi slash pi_i$ — циклическая группа порядка $m_i$. Выберем
образующий $s=f (t)$ группы $sigma_i$ $(t in pi)$. Тогда
$R sigma_i=R [s]=R [S] slash (P (S))$, где
$ P (S)=S^(m_i)-1=product_(j in J) P_j (S) $
— разложение многочлена $P$ в произведение приведенных неприводимых многочленов
кольца $L [S]$. Заметим, что здесь используется то же самое множество $J$, что и
введенное выше, и мы имеем
$ L sigma_i=L [s]=L [S] slash (P (S))=product_(j in J) L [S] slash (P_j (S)). $
Так как кольцо $R$ целозамкнуто, то коэффициенты каждого из многочленов $P_j$
лежат в $R$ и
$
  A_j=R [S] slash (P_j (S))=A' slash (f (frak(p)_j)), quad
  "где" f (frak(p)_j)=P_j (s) A'.
$
Можно описать $P_j (S)$ как минимальный многочлен элемента
$rho'_j (s)=rho_j (t)$ над полем $L$. В частности, если $j=i$, то $w=rho_i (t)$
является примитивным корнем $m_i$-й степени из единицы и $A_i=R [w]$. Положим
$ Q (S)=product_(j!=i) P_j (S)=(S^(m_i)-1) slash (P_i (S)). $
Тогда ясно, что аннулятор элемента $f (frak(p)_i)=P_i (s) R [s]$ в кольце $A'$
равен $Q (s) R [s]$. Заметим, что $Q (s)=Q (f (t))=f (Q (t))$.

Теперь можно применить полученное выше утверждение
@eq:conductor-principal-component. Здесь $N_i$ играют роль $N$ (в силу
@eq:group-augmentation-annihilator), а $Q (t)$ играет роль элемента $d$ в
@eq:conductor-principal-component. Сформулируем наши выводы в следующем виде:

#proposition[
  Сохраним введенные выше обозначения @eq:abelian-group-ring-conductor-data и
  @eq:abelian-group-cyclotomic-quotient. Пусть $frak(p)_i=Ker (rho_i:A -> A_i)$
  $(i in I)$ и $frak(c)=frak(c)_(B slash A)$ — кондуктор. Тогда
  $ frak(c)=union.sq.big_(i in I) frak(c)_i, $
  где $frak(c)_i=ann_A (frak(p)_i)$ и $rho_i (frak(c))=rho_i (frak(c)_i)$.
  Выберем $t in pi$ так, чтобы элемент $w=rho_i (t)$ порождал группу
  $mu_(m_i)=rho_i (pi)$. Положим $Q (T)=(T^(m_i)-1) slash (P (T))$, где $P (T)$
  — минимальный многочлен элемента $w$ над полем $L$. Пусть
  $N_i=sum_(x in pi_i) x$, где $pi_i=Ker (rho_i:pi -> mu_(m_i))$. Тогда
  $ frak(c)_i=N_i Q (t) A $
  <eq:abelian-group-conductor-component>
  и, следовательно,
  $ rho_i (frak(c)_i)=(m slash m_i) Q (w) R [w]. $
  <eq:abelian-group-conductor-component-image>
] <prop:abelian-group-ring-conductor>

Для завершения вычислений нам хотелось бы получить более явное описание идеала
$Q (w) R [w]$ из равенства @eq:abelian-group-conductor-component-image.
Попробуем #source(466)осуществить это в том случае, когда $R$ — кольцо
циклотомических целых величин.

Для целого числа $m>=1$ положим
$ R_m=ZZ [mu_m], quad L_m=QQ [mu_m]. $
(В §~@sec:classical-induction-theorems использовались соответственно обозначения
$ZZ_m$ и $QQ_m$.) Известно, что $R_m$ является кольцом всех целых алгебраических
чисел (оно совпадает с целым замыканием кольца $ZZ$) в поле $L_m$. Положим
$
  Phi_m={"примитивные корни" m "-й степени из единицы"}
  ={"образующие элементы группы" mu_m}.
$
Тогда группа $mu_m$ является дизъюнктивным объединением множеств $Phi_d$
$(d divides m)$ и $[L_m:QQ]=card (Phi_m)=phi (m)$ ($phi$ — функция Эйлера).
Заметим, что
$
  T^m-1=product_(d divides m) phi_d (T), quad
  "где" phi_d (T)=product_(w in Phi_d) (T-w)
$
является _циклотомическим многочленом_.

#proposition[
  Пусть $w in Phi_m$ $(m>1)$. Тогда
  $
    Nr_(L_m slash QQ) (1-w)=phi_m (1)=cases(
      p & "если" m "является степенью простого числа" p comma,
      1 & "в противном случае."
    )
  $
] <prop:cyclotomic-one-minus-root-norm>

#proof[
  Так как $Phi_m$ совпадает с множеством сопряженных с $w$ элементов над $QQ$,
  то $Nr_(L_m slash QQ) (1-w)=product_(u in Phi_m) (1-u)=phi_m (1)$. Если число
  $p$ простое, то $phi_p (T)=1+T+dots+T^(p-1)$ и
  $phi_(p^n) (T)=phi_p (T^(p^(n-1)))$ для $n>=1$. Следовательно,
  $phi_(p^n) (1)=p$, что доказывает предложение для степеней простых чисел.
  Предположим, что число $m$ составное#footnote[Под составным числом здесь
    подразумевается число, имеющее по крайней мере два простых делителя. —
    _Прим. перев._] и что нам известен (по индукции) результат для всех
  собственных делителей числа $m$. Получаем
  $ 1+T+dots+T^(m-1)=product_(d divides m comma d>1) phi_d (T). $
  Поэтому $m=product_(d divides m comma d>1) phi_d (1)$. Правая часть равна
  произведению $phi_m (1)$ на произведение всех $phi_d (1)$
  $(d divides m,1<d<m)$. В силу индуктивного предположения $phi_d (1)=1$ для
  входящих сюда составных чисел $d$. Если $m=p^n m'$, где простое число $p$
  #source(467)не делит $m'$, то мы получим $n$ множителей $phi_(p^i) (1)=p$
  $(1<=i<=n)$, которые вместе дают множитель $p^n$. Варьируя теперь $p$, видим,
  что число $product_(d divides m comma 1<d<m) phi_d (1)$ равно $m$. Из
  приведенного выше равенства получаем, что $m=phi_m (1) dot m$. Поэтому
  $phi_m (1)=1$. Тем самым предложение доказано.
]

#corollary[
  Пусть $u,v in Phi_m$ $(m>1)$. Тогда $(1-u) slash (1-v)$ — («циклотомический»)
  обратимый элемент кольца $R_m$. Если число $m$ составное, то обратим уже сам
  элемент $1-u$.
] <cor:equal-order-root-unit-quotient>

#proof[
  Мы можем записать, что $u=v^i$. Поэтому
  $(1-u) slash (1-v)=1+v+dots+v^(i-1) in R_m$. В силу симметрии обратный элемент
  также лежит в $R_m$. В свою очередь из @prop:cyclotomic-one-minus-root-norm
  получаем, что норма этого элемента (над $QQ$) равна единице. Так как это
  алгебраическое число, то оно должно быть обратимым элементом. Это рассуждение
  также применимо и к элементу $1-u$ для составного числа $m$.
]

Это следствие показывает, что элементы $1-u$ и $1-v$ порождают один и тот же
идеал кольца $R_m$ и, следовательно, любого кольца, содержащего кольцо $R_m$.
Кроме того, если число $m$ составное, то этот идеал совпадает со всем кольцом.
Если $m=p^n$, где число $p$ простое, то этот идеал зависит лишь от $p^n$. Так
как $p=product_(v in Phi_(p^n)) (1-v)$ и
$card (Phi_(p^n))=phi (p^n)=(p-1) p^(n-1)$, то #numbered-condition[
  $(1-u)^(phi (p^n))=(p)$ или $(1-u)=(p)^(1 slash phi (p^n))$ для всякого
  простого числа $p$ и всех $u in Phi_(p^n)$.
] <eq:cyclotomic-root-principal-ideal>
Эти равенства можно интерпретировать как соотношения между главными идеалами
кольца $R_(p^n)$ или, более общим образом, любой области целостности, содержащей
кольцо $R_(p^n)$. В целозамкнутой области второе равенство означает, что $(1-u)$
является единственным главным идеалом, который в степени $phi (p^n)$ дает $(p)$.
Приведенное выше равенство можно переписать так: #numbered-condition[
  $(p)=product_(u in Phi_(p^n)) (1-u)$ для каждого $n>=1$.
] <eq:cyclotomic-prime-ideal-product>

#proposition[
  Пусть $m$ и $n$ — натуральные числа, $m=product_p p^(m_p)$ и
  $n=product_p p^(n_p)$ — их разложения на простые множители. Пусть
  $h_p=max (m_p,n_p)$ и $r_p=min (m_p,n_p)$. Таким образом,
  $h=product_p p^(h_p)=Lcm (m,n)$ и $r=product_p p^(r_p)=Gcd (m,n)$. Пусть
  $P (T)$ — минимальный многочлен элемента $w in Phi_m$ над $L_n$. Положим
  $Q (T)=(T^m-1) slash (P (T))$. Тогда
  $ Q (w) R_n [w]=product_(p divides m) (p)^(s_p), $
  <eq:cyclotomic-conductor-ideal-product>
  #source(468)где
  $
    s_p=cases(
      1 slash (p-1) & "если" p divides.not n "(т. е. если" n_p=0 ")"
                      comma,
      r_p=min (m_p,n_p) & "если" p divides n "(т. е. если" n_p>0 ")."
    )
  $
  Если $p divides m$ и $frak(p)$ — простой идеал кольца $R_n [w]$ $(=R_h)$,
  делящий $p$, то
  $
    v_frak(p) (Q (w) R_n [w])=cases(
      p^(h_p-1) & "если" p divides.not n comma,
      r_p (p-1) p^(h_p-1) & "если" p divides n.
    )
  $
  <eq:cyclotomic-conductor-valuation>
] <prop:cyclotomic-conductor-valuation>

_Замечание._ Ясно, что $R_n [w]=R_h$. Кроме того, из того факта, что $p$
полностью разветвляется в поле деления круга на $k$ частей, где $k$ — степень
числа $p$, и вовсе не разветвляется в $R_m$, если число $m$ взаимно просто с
$p$, вытекает равенство
$ v_frak(p) (p)=phi (p^(h_p))=(p-1) p^(h_p-1). $
Таким образом, $v_frak(p) ((p)^(s_p))=s_p phi (p^(h_p))$. Поэтому равенство
@eq:cyclotomic-conductor-valuation следует из равенства
@eq:cyclotomic-conductor-ideal-product.

Отметим теперь, что в экстремальных случаях предложение дает нам
$
  Q (w) R_n [w]=cases(
    product_(p divides m) (p)^(1 slash (p-1)) & "если" Gcd (m,n)=1 comma,
    (m) & "если" m divides n.
  )
$
<eq:cyclotomic-conductor-extreme-cases>

#proof(
  head: [#emph[
    Доказательство предложения @prop:cyclotomic-conductor-valuation.
  ]],
)[
  В силу сделанного выше замечания надо доказать лишь равенство
  @eq:cyclotomic-conductor-ideal-product. Пусть $C$ — множество элементов,
  сопряженных с $w$ над $L_n$. Тогда $C subset Phi_m$ и
  $Q (T)=product_(u in mu_m without C) (T-u)$. Идеал, порожденный элементом
  $w-u=w (1-u w^(-1))$, зависит лишь от порядка элемента $u w^(-1)$. Этот идеал
  совпадает со всем кольцом, если порядок элемента $u w^(-1)$ составной (см.
  @cor:equal-order-root-unit-quotient). Кроме того, в силу равенств
  @eq:cyclotomic-root-principal-ideal, если порядок элемента $u w^(-1)$ равен
  степени простого числа $p$, идеал $(1-u w^(-1))$ является некоторой дробной
  степенью идеала $(p)$. Следовательно, мы получаем некоторую формулу типа
  $ Q (w) R_n [w]=product_(p divides m) (p)^(s_p), $
  в которой нам надо определить рациональные числа $s_p$.

  Зафиксируем простой делитель $p$ числа $m$. Положим $q=p^(m_p)$. Надо найти
  элемент $u in mu_m without C$, для которого порядок элемента $u w^(-1)$ равен
  степени числа $p$. Пусть $w=w_0 w_1$, где $w_0 in mu_q$ и порядок элемента
  $w_1$ взаимно прост с $p$. (Так как $w in Phi_m$, то $w_0 in Phi_q$.)
  Аналогичным образом разложим элемент $u=u_0 u_1$. Тогда
  $u w^(-1) in mu_q <=> u_1=w_1$. В этом случае элемент $u$ не является
  $L_n$-сопряженным с $w$ тогда и только тогда, когда элемент $u_0$ не является
  $L_n$-сопряженным с $w_0$. Итак, если $C_p$ — множество всех элементов,
  #source(469)$L_n$-сопряженных с $w_0$, то
  $ (p)^(s_p)=product_(u_0 in mu_q without C_p) (1-u_0 w_0^(-1)). $
  Но $Aut (mu_q) tilde.eq U (ZZ slash (q ZZ))=U (ZZ slash (p^(m_p) ZZ))$, и
  автоморфизмы, индуцированные с помощью $Gal (L_n (w_0) slash L_n)$,
  соответствуют «конгруэнц-группе» уровня $p^(r_p)=Gcd (q,n)$, т. е.
  автоморфизмам, оставляющим неподвижным множество $mu_(p^(r_p))$. (Именно здесь
  мы существенно использовали то, что поле $L_n$ является циклотомическим, а не
  произвольным числовым полем.) Из этого следует, что
  $
    C_p=cases(
      Phi_q=mu_(p^(m_p)) without mu_(p^(m_p-1)) & "если" p divides.not n ";",
      w_0 mu_(p^(t_p)) comma quad t_p=max (0,m_p-n_p) & "если" p divides n.
    )
  $
  Таким образом,
  $
    w_0^(-1) (mu_(p^(m_p)) without C_p)=cases(
      w_0^(-1) mu_(p^(m_p-1)) & "если" p divides.not n ";",
      w_0^(-1) mu_(p^(m_p)) without mu_(p^(t_p))
      =mu_(p^(m_p)) without mu_(p^(t_p)) & "если" p divides n.
    )
  $
  Но $w_0^(-1) mu_(p^(m_p-1)) subset Phi_(p^(m_p))$ и
  $mu_(p^(m_p)) without mu_(p^(t_p))=union.sq.big_(t_p<i<=m_p) Phi_(p^i)$.
  Следовательно, применяя @eq:cyclotomic-root-principal-ideal и
  @eq:cyclotomic-prime-ideal-product, получаем
  $
    (p)^(s_p)=product_(u in mu_q without C_p) (1-u w_0^(-1))=cases(
      (p)^(p^(m_p-1) slash phi (p^(m_p)))=(p)^(1 slash (p-1))
      & "если" p divides.not n ";",
      (p)^(m_p-t_p) & "если" p divides n.
    )
  $
  Так как $m_p-t_p=m_p-max (0,m_p-n_p)=min (m_p,n_p)$, то предложение доказано.
]

#corollary[
  В ситуации предложения @prop:abelian-group-ring-conductor допустим, что
  $R=R_n$. Тогда в обозначениях предложения @prop:abelian-group-ring-conductor
  кольцо $B=product A_i$ является целым замыканием кольца $A=R_n pi$ в $L_n pi$.
  Кроме того,
  $ rho_i (frak(c))=(m slash m_i) product_(p divides m_i) (p)^(s_p), $
  где
  $
    s_p=cases(
      1 slash (p-1) & "если" p divides.not n ";",
      min (v_p (m_i),v_p (n)) & "если" p divides n.
    )
  $
  Следовательно, $m B subset frak(c)$ и
  $B slash sqrt(frak(c))=B slash sqrt(m B)$. (Здесь через $v_p (m)$ обозначена
  степень элемента $p$, делящая число $m$.) Кондуктор $frak(c)$ совпадает
  #source(470)со своим собственным радикалом в кольце $B$ тогда и только тогда,
  когда число $m=[pi:1]$ не содержит квадратов (и поэтому группа $pi$
  циклическая) и либо $Gcd (m,n)=1$, либо $Gcd (m,n)=2$ и $4 divides.not n$.
] <cor:cyclotomic-group-ring-conductor>

#proof[
  Как было замечено выше, кольцо $B$ является целым над $A$ и целозамкнутым.
  Таким образом, мы получаем первое утверждение. В силу
  @prop:abelian-group-ring-conductor
  $rho_i (frak(c)_i)=(m slash m_i) Q (w) R_n [w]$. Предложение
  @prop:cyclotomic-conductor-valuation, как и выше, говорит о том, что
  $Q (w) R_n [w]=product_(p divides m_i) (p)^(s_p)$. Так как все $s_p>0$, то
  каждый простой идеал в $A_i$, делящий $p$, делит $rho_i (frak(c)_i)$, если
  $p divides m_i$. Это же, очевидно, верно и в том случае, если
  $p divides (m slash m_i)$. Следовательно, радикалы идеалов $rho_i (frak(c)_i)$
  и $m A_i$ в $A_i$ совпадают. Из @eq:cyclotomic-conductor-ideal-product
  следует, что $m B subset frak(c)$. Последнее утверждение получаем простым, но
  утомительным анализом случаев, используя @eq:cyclotomic-conductor-valuation.
  Детали мы оставляем читателю. Случай, когда $m$ и $n$ взаимно просты, можно
  вывести из следующего, более точного утверждения:
]

#corollary[
  Пусть в ситуации следствия @cor:cyclotomic-group-ring-conductor $Gcd (m,n)=1$
  (например, если $n=1$, то $A=ZZ pi$). Тогда
  $
    rho_i (frak(c)_i)=(m slash m_i) product_(p divides m_i) (p)^(1 slash (p-1)).
  $
  Пусть число $p$ простое и $frak(p)$ — простой идеал кольца $A_i$, делящий $p$.
  Пусть $t=v_p (m_i)$. Тогда
  $
    v_frak(p) (rho_i (frak(c)_i))=cases(
      p^(t-1) (v_p (m slash m_i) (p-1)+1) & "если" t>0 ";",
      v_p (m slash m_i) & "если" t=0.
    )
  $
] <cor:coprime-cyclotomic-group-ring-conductor>

#proof[
  Первое утверждение вытекает из @cor:cyclotomic-group-ring-conductor. Второе
  следует из первого, поскольку $v_frak(p) (p)=phi (p^t)$ и
  $phi (p^t)=(p-1) p^(t-1)$, если $t>0$, что и требовалось доказать.
]

Для последующих приложений нам потребуются следующие формулы:

#proposition[
  Пусть $A=ZZ pi$, где $pi$ — абелева группа порядка $m=[pi:1]$. Пусть $B$ —
  целое замыкание кольца $A$ в алгебре $QQ pi$ и $frak(c)$ — кондуктор из $B$ в
  $A$. Если простое число $p$ делит $m$, то пусть $pi=pi_p times pi'_p$, где
  $pi_p$ — силовская $p$-подгруппа. Тогда
  $
    h_0 (A)=1; \ h_0 (B)=h_0 (QQ pi)=product_(p divides m) h_0 (QQ pi_p); \
    h_0 (A slash frak(c))=sum_(p divides m) h_0 (FF_p pi'_p); \
    h_0 (B slash frak(c))=sum_(p divides m) h_0 (QQ pi_p) h_0 (FF_p pi'_p).
  $
  Абелева группа
  $ M=Coker (H_0 (B) plus.o H_0 (A slash frak(c)) -> H_0 (B slash frak(c))) $
  #source(471)является свободной ранга
  $ h_0 (A)-(h_0 (B)+h_0 (A slash frak(c)))+h_0 (B slash frak(c)). $
  Она является нулем тогда и только тогда, когда $m$ — степень простого числа.
] <prop:abelian-group-conductor-component-ranks>

#proof[
  Из @th:group-ring-projective-local-freeness следует, что $h_0 (A)=1$. Ясно,
  что $h_0 (B)=h_0 (QQ pi)$.

  Если числа $m$ и $n$ взаимно просты, то поля $L_m$ и $L_n$ линейно свободны
  над полем $QQ$. Поэтому $L_m tensor_(QQ) L_n tilde.eq L_(m n)$ и
  $R_m tensor_(ZZ) R_n tilde.eq R_(m n)$. Пусть порядок группы $pi'$ равен $n$ и
  $B'$ — целое замыкание кольца $A'=ZZ pi'$ в $QQ pi'$. Из уже сделанных
  замечаний следует (поскольку $QQ [pi times pi']=QQ pi tensor_(QQ) QQ pi'$ и
  аналогичное утверждение имеет место для кольца $ZZ [pi times pi']$), что
  $h_0 (QQ [pi times pi'])=h_0 (QQ pi) dot h_0 (QQ pi')$ и что
  $B tensor_(ZZ) B'$ является целым замыканием кольца $ZZ [pi times pi']$.
  Первое из этих утверждений влечет за собой следующее:
  $ h_0 (QQ pi)=product_(p divides m) h_0 (QQ pi_p). $
  Так как радикалы идеалов $frak(c)$ и $m B$ в $B$ совпадают (см.
  @cor:cyclotomic-group-ring-conductor), то они совпадают и в $A$, и можно для
  вычисления $h_0$ вместо $frak(c)$ использовать $m B$. Кроме того,
  $m^2 B subset m A subset m B$. Поэтому
  $h_0 (B slash frak(c))=h_0 (B slash (m B))$ и
  $h_0 (A slash frak(c))=h_0 (A slash (m A))$. Очевидно,
  $
    h_0 (A slash (m A))=sum h_0 (A slash (p A))=sum h_0 (FF_p pi)
    =sum h_0 (FF_p pi'_p).
  $
  Суммирование проводится по всем $p$, делящим $m$. Последнее равенство имеет
  место, поскольку группа $pi_p$ действует тривиально на простых
  $FF_p pi$-модулях.

  Аналогично $h_0 (B slash (m B))=sum h_0 (B slash (p B))$. Для данного $p$
  разложение $B=B_p tensor_(ZZ) B'_p$ соответствует разложению группы
  $pi=pi_p times pi'_p$ (как в предыдущем абзаце). В каждом из множителей $B_p$
  $p$ полностью разветвляется. Поэтому $B_p slash (p B_p)$ является
  произведением $h_0 (QQ pi_p)$, т. е. артиновых локальных колец с полями
  вычетов $FF_p$. Кроме того, так как порядок группы $pi'_p$ взаимно прост с
  $p$, то $ZZ$-локализации колец $B'_p$ и $ZZ pi'_p$ в $p$ совпадают. Поэтому
  $B'_p slash (p B'_p)=(ZZ pi'_p) slash (p (ZZ pi'_p))=FF_p pi'_p$. Таким
  образом, по модулю нильпотентного идеала
  $B slash (p B)=(B_p slash (p B_p)) tensor_(ZZ) (B'_p slash (p B'_p))$
  превращается в произведение $h_0 (QQ pi_p)$ экземпляров колец $FF_p pi'_p$.
  Итак, $h_0 (B slash frak(c))=sum h_0 (QQ pi_p) h_0 (FF_p pi'_p)$.

  Декартов квадрат
  $ #conductor-square() $
  приводит нас к точной последовательности (см.
  @prop:milnor-spectrum-rank-pushout)
  $
    0 -> H_0 (A) -> H_0 (B) plus.o H_0 (A slash frak(c)) arrow.r^h
    H_0 (B slash frak(c)),
  $
  в которой $M=Coker (h)$ является абелевой группой без кручения. Так как группа
  $M$ конечно порождена, то $M$ — свободная абелева #source(472)группа
  указанного ранга. Если число $m$ — степень простого числа $p$, то из
  приведенной формулы следует, что $h_0 (A slash frak(c))=1$ и
  $h_0 (B slash frak(c))=h_0 (QQ pi)$. Таким образом, $M=0$.

  Наконец, предположим, что $m=m_q m'$, где $m_q$ — степень простого числа $q$ и
  число $m'>1$ взаимно просто с $q$. Покажем, что $M!=0$. Что касается ранга
  группы $M$, то
  $
    r (pi)=1-h_0 (QQ pi)+sum_p h_0 (QQ pi_p) (h_0 (FF_p pi'_p)-1)
    =1-h_0 (QQ pi_q) h_0 (QQ pi'_q)
    +sum_(p!=q) h_0 (QQ pi_p) (h_0 (FF_p pi'_p)-1)
    +h_0 (QQ pi_q) (h_0 (FF_q pi'_q)-1)
    =1-h_0 (QQ pi'_q)+sum_(p!=q) h_0 (QQ pi_p) (h_0 (FF_p pi'_p)-1)
    +h_0 (QQ pi_q) (h_0 (FF_q pi'_q)-h_0 (QQ pi'_q))
    >r (pi'_q)+h_0 (QQ pi_q) (h_0 (FF_q pi'_q)-h_0 (QQ pi'_q))>=0.
  $
  Последнее неравенство имеет место, поскольку $r (pi'_q)>=0$ и
  $h_0 (FF_q pi'_q)>=h_0 (QQ pi'_q)$ (так как порядок группы $pi'_q$ взаимно
  прост с $q$). Строгое неравенство получается при замене членов
  $h_0 (FF_p pi'_p)$ (с $p!=q$) на строго меньшие члены $h_0 (FF_p pi''_p)$, где
  $pi'_p=pi_q times pi''_p$. Это завершает доказательство.
]
