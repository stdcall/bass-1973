#import "main-defs.typ": (
  Aut, Coker, G, Gcd, H, Im, K, Ker, Nr, SK, U, cyclicClass, idx, maxSpec,
  name-idx, rank, source, spec, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, numbered-condition, proof, proposition,
  theorem,
)
#import "diagrams/finite-group-induction-applications.typ": (
  abelian-group-g-one-triangle, finite-group-k-one-cartan,
)

#heading(level: 2)[Применения к группам $K_1 (R pi)$ и $G_1 (R pi)$]
<sec:group-ring-k1-g1-applications>

Для первой части этого параграфа зафиксируем следующие обозначения:
#numbered-condition[
  $R$ — кольцо целых алгебраических чисел в числовом поле $L$;

  $pi$ — абелева группа порядка $m=[pi:1]$;

  $A=R pi$;

  $B$ — целое замыкание кольца $A$ в $L pi$;

  $frak(c)$ — кондуктор из $B$ в $A$.
] <eq:abelian-group-ring-arithmetic-data>
Как и в @prop:abelian-group-ring-conductor, $B=product A_i$ и проекции
$rho_i:A -> A_i$ сюръективны. Кроме того, $frak(c)=union.sq.big frak(c)_i$, где
$frak(c)_i$ изоморфно проектируется на свой образ в $A_i$.

#theorem[
  #condition-list[
    #condition-item(format: "cyrillic")[(Хигман)#idx("теорема", "Хигмана")
      Каждый обратимый элемент конечного порядка группового кольца $R pi$ имеет
      вид $u x$, где $u$ — корень из единицы в $R$ и $x in pi$.]
    <cond:higman-group-ring-torsion-units>
    #source(473)#condition-item(format: "cyrillic")[$U (R pi)$ — конечно
      порожденная абелева группа ранга $h_0 (RR tensor_(QQ) L pi)-h_0 (L pi)$.]
    <cond:abelian-group-ring-unit-rank>
    #condition-item(format: "cyrillic")[(Милнор)#idx("теорема", "Милнора") Пусть
      $U' (R pi)$ — подгруппа группы $U (R pi)$, порожденная всеми $U (R pi')$,
      где $pi'$ пробегает все циклические подгруппы группы $pi$. Тогда
      $U (R pi) slash (U' (R pi))$ — конечная группа экспоненты
      $e_(cyclicClass) (L,pi)^2$.]
    <cond:cyclic-induction-group-ring-units>
  ]
] <th:abelian-group-ring-units>

Напомним (см. @cor:rational-induction-exponent-bound), что число
$e_(cyclicClass) (L,pi)$ делит число $e_(cyclicClass) (QQ,pi)$, а последнее в
свою очередь делит $m$ (см. @th:artin-lam-cyclic-induction-exponents).

#proof[
  @cond:higman-group-ring-torsion-units Мы используем соотношение
  ортогональности для характеров.

  Очевидно, можно считать, что поле $L$ достаточно велико для группы $pi$. Пусть
  $e_1,dots,e_m$ — примитивные идемпотенты алгебры $L pi tilde.eq L^m$. Если
  $x in pi$, то $x=sum rho_i (x) dot e_i$. Следовательно, если $a=sum a_x x$
  $(x in pi)$, то $rho_i (a)=sum a_x rho_i (x)$. Нам необходимо такое следствие
  из соотношений ортогональности (см. Кэртис и Райнер @bib:Curtis1962)
  $ a_x=m^(-1) sum_(1<=i<=m) rho_i (a) rho_i (x^(-1)), $
  где каждый член суммы мы рассматриваем как элемент из $L$. Предположим теперь,
  что $a in U (R pi)$ и что порядок элемента $a$ конечен. Для любого вложения
  поля $L$ в поле $CC$ получаем
  $ abs(a_x)<=abs(m)^(-1) sum_(1<=i<=m) abs(rho_i (a) rho_i (x^(-1)))<=1, $
  поскольку $rho_i (a)$ и $rho_i (x)$ являются корнями из единицы для каждого
  $i$. Следовательно, модуль числа $Nr_(L slash QQ) (a_x)$ (являющегося
  произведением чисел, (комплексно) сопряженных с $a_x$), не больше $1$. Но
  $a_x in R$ — алгебраические числа. Поэтому $abs(Nr_(L slash QQ) (a_x))=0$ или
  $abs(Nr_(L slash QQ) (a_x))=1$. Если $a_x!=0$, то, таким образом,
  $rho_i (a) rho_i (x^(-1))=a_x$ для всех $i$ (в противном случае указанное выше
  неравенство было бы строгим). Итак, $rho_i (a)=a_x rho_i (x)=rho_i (a_x x)$
  для всех $i$. Поэтому $a=a_x x$, где элемент $x$ выбран так, что $a_x!=0$.

  @cond:abelian-group-ring-unit-rank Это утверждение следует из теоремы Дирихле
  о единицах @th:dirichlet-units, так как индекс подгруппы $U (A)$ в группе
  $U (B)$ конечен, поскольку подгруппа $U (A)$ содержит
  $U (B,frak(c))=Ker (U (B) -> U (B slash frak(c)))$.

  @cond:cyclic-induction-group-ring-units Можно отождествить $U (R pi)$ и образ
  отображения $K_1 (R pi) -> K_1 (L pi)$. Тогда мы получаем фробениусов модуль
  над фробениусовым функтором $G_R$, при этом группа $U' (R pi)$ есть не что
  иное, как $U_(cyclicClass) (R pi)$. Поэтому ее экспонента в $U (R pi)$ равна
  $e_(cyclicClass) (R,pi)$ (см. @prop:induction-exponent-module-bound). В силу
  @prop:induction-exponent-dedekind-ring число $e_(cyclicClass) (R,pi)$ делит
  число $e_(cyclicClass) (L,pi)^2$.

  Теорема доказана.
]

#source(474)Теорему @th:abelian-group-ring-units (часть
@cond:cyclic-induction-group-ring-units) можно применить для задания образующими
и соотношениями подгруппы конечного индекса группы $U (ZZ pi)$ (см.
Басс#name-idx("Басс (Bass H.)") @bib:Bass1966a).

#theorem[
  Допустим, что в рассмотренной выше ситуации $R=ZZ$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[естественный гомоморфизм
      $ SK_1 (A,frak(c)) -> SK_1 (A) $
      сюръективен и
      $
        SK_1 (A,frak(c))=SK_1 (B,frak(c))
        =union.sq.big_i SK_1 (A_i,rho_i (frak(c)_i)).
      $]
    <cond:integral-group-ring-relative-sk1-surjection>
    #condition-item(format: "cyrillic")[Если $pi_i=Ker (rho_i (pi))$,
      $m_i=[pi:pi_i]$ и $n_i=[pi_i:1]$, то
      $ SK_1 (A_i,rho_i (frak(c)_i)) tilde.eq mu_(r_i), $
      где $mu_(r_i)$ — группа корней $r_i$-й степени из единицы в $A_i$, а
      $
        r_i=cases(
          1 & "если" m_i<=2 ";",
          2 Gcd (m_i,n_i) & "если" m_i>2 "нечетно и" 4 divides n_i ";",
          Gcd (m_i,n_i) & "в противном случае."
        )
      $]
    <cond:integral-group-ring-conductor-sk1-roots>
  ]
  Следовательно, экспонента группы $SK_1 (A,frak(c))$ (а потому и группы
  $SK_1 (A)$) равна $e$, где $e=exp (pi)$.
] <th:integral-abelian-group-ring-sk1>

#proof[
  @cond:integral-group-ring-relative-sk1-surjection Так как кольцо
  $A slash frak(c)$ полулокально, то сюръективность отображения
  $SK_1 (A,frak(c)) -> SK_1 (A)$ вытекает из
  @cor:semilocal-relative-special-linear-surjection. Последнее утверждение части
  @cond:integral-group-ring-relative-sk1-surjection следует из
  @prop:subdirect-product-relative-k-one-excision.

  @cond:integral-group-ring-conductor-sk1-roots Заметим, что
  $A_i=ZZ [mu_(m_i)]$, где $mu_(m_i)=rho_i (pi)$. Поэтому число корней из
  единицы в $A_i$ равно
  $
    m'_i=cases(
      m_i & "если" 2 divides m_i ";",
      2 m_i & "если" 2 divides.not m_i.
    )
  $
  Из @th:bass-milnor-serre-reciprocity следует, что
  $SK_1 (A_i,rho_i (frak(c)_i)) tilde.eq mu_(r_i)$, где $r_i=1$, если $m_i<=2$
  (т. е. если $A_i=ZZ$); в противном случае число $r_i$ определяется так:
  $ r_i=product_(p divides m'_i) p^(j_p), $
  где $j_p$ — целое число из интервала $[0,v_p (m'_i)]$, ближайшее к числу
  $
    min_(frak(p) divides p A_i)
    floor(v_frak(p) (rho_i (frak(c)_i)) slash (v_frak(p) (p)) - 1 slash (p-1)).
  $
  В силу @cor:coprime-cyclotomic-group-ring-conductor
  $
    rho_i (frak(c)_i)=(m slash m_i) product_(p divides m_i) (p)^(1 slash (p-1)).
  $
  Итак, если $p divides m_i$ и $frak(p) divides p$, то, поскольку
  $n_i=m slash m_i$,
  $
    v_frak(p) (rho_i (frak(c)_i))=v_frak(p) (n_i)+(1 slash (p-1)) v_frak(p) (p)
  $
  #source(475)и
  $ v_frak(p) (n_i) slash (v_frak(p) (p))=v_p (n_i). $
  Поэтому
  $ j_p=min (v_p (m_i),v_p (n_i)). $
  Это показывает, что числа $r_i$ и $Gcd (m_i,n_i)$ совпадают во всех
  факторкольцах, соответствующих простым числам, которые делят число $m_i$. Так
  как число $r_i$ делимо лишь простыми числами, которые делят число $m'_i$, то
  остается лишь случай, когда $p=2$ и $m_i>2$, при этом $m_i$ — нечетное число.
  Если $frak(p) divides 2$, то
  $v_frak(p) (rho_i (frak(c)))=v_frak(p) (m slash m_i)=v_frak(p) (n_i)$ и
  $1 slash (2-1)=1$. Поэтому $j_2$ — целое число из интервала
  $[0,v_2 (m'_i)=1]$, ближайшее к числу $v_2 (n_i)-1$. Таким образом, $j_2=0$,
  если $v_2 (n_i)<=1$ (т. е. $4 divides.not n_i$), и $j_2=1$, если
  $4 divides n_i$. Тем самым получена формула для числа $r_i$. Из нее следует,
  что $r_i divides m_i$ или $r_i divides 2 m_i$, если число $m_i$ нечетно, а
  число $m$ четно. Следовательно, в любом случае число $r_i$ делит число
  $e=exp (pi)$. Из части @cond:integral-group-ring-relative-sk1-surjection
  теперь получаем, что $SK_1 (A,frak(c))$ и $SK_1 (A)$ — группы экспоненты $e$.
  Доказательство закончено.
]

#proposition[
  В ситуации теоремы @th:integral-abelian-group-ring-sk1 допустим, что для
  некоторого простого числа $p$ силовская $p$-подгруппа $pi_p$ группы $pi$
  является циклической. Тогда группа $SK_1 (ZZ pi)$ без $p$-кручения.
  Следовательно, $SK_1 (ZZ pi)=0$, если $pi$ — циклическая группа.
] <prop:cyclic-sylow-group-ring-sk1-torsion-free>

#proof[
  Пусть $p^n=[pi_p:1]$. Проведем индукцию по $n$. Случай $n=0$ разобран в
  @th:integral-abelian-group-ring-sk1@cond:integral-group-ring-conductor-sk1-roots.
  Допустим, что $n>0$ и $pi'=pi slash sigma$, где $sigma$ — подгруппа порядка
  $p$. Пусть $frak(a)=Ker (ZZ pi -> ZZ pi')$. Тогда рассмотрим точную
  последовательность
  $ SK_1 (ZZ pi,frak(a)) -> SK_1 (ZZ pi) -> SK_1 (ZZ pi'), $
  в которой группа, стоящая справа, без $p$-кручения (по индуктивному
  предположению). Ясно, что $frak(a)$ содержит все компоненты $frak(c)_i$
  кондуктора $frak(c)$, для которых $rho_i (sigma)!={1}$. Кроме того, если
  $frak(b)$ — сумма таких компонент $frak(c)_i$, то индекс $frak(b)$ в $frak(a)$
  конечен. (Они являются $ZZ$-решетками в одном и том же двустороннем идеале
  кольца $QQ pi$.) В силу @cor:annihilator-semilocal-sk-one-surjection
  отображение $SK_1 (ZZ pi,frak(b)) -> SK_1 (ZZ pi,frak(a))$ сюръективно. Кроме
  того, из @prop:subdirect-product-relative-k-one-excision следует, что
  $SK_1 (ZZ pi,frak(b))=SK_1 (B,frak(b))$, так как $frak(b)$ является
  $B$-идеалом. Но группа $SK_1 (B,frak(b))$ является прямой суммой тех групп
  $SK_1 (A_i,rho_i (frak(c)_i))$, для которых $rho_i (sigma)!={1}$. Поэтому
  доказательство будет завершено, если мы покажем, что это группы без
  $p$-кручения. Из условия $rho_i (sigma)!={1}$ следует, что $rho_i$ действует
  точно на группе $pi_p$, поскольку последняя группа циклическая. Таким образом,
  в обозначениях теоремы @th:integral-abelian-group-ring-sk1 $p^n divides m_i$ и
  $p divides.not n_i$. Итак, в этом случае
  $SK_1 (A_i,rho_i (frak(c)_i)) tilde.eq mu_(r_i)$, где
  $v_p (r_i)<=min (v_p (n_i),v_p (m_i))=0$. Тем самым доказательство окончено.
]

#source(476)_Замечание._ Неизвестны примеры рассмотренных выше абелевых групп
$pi$, для которых $SK_1 (ZZ pi)!=0$. Лэм @bib:Lam1967 и Кервер (неопубликовано)
показали, что $SK_1 (ZZ pi)=0$, если $pi$ — абелева $p$-группа с двумя
образующими, порядок одного из которых равен $p$. Лэм также показал, что
$SK_1 (ZZ pi)$ — группа без $p$-кручения, если $pi$ — любая конечная абелева
группа, для которой $[pi_p:1]=p^2$. Если существует пример абелевой группы $pi$,
для которой $SK_1 (ZZ pi)!=0$, то кажется вероятным, что такой пример должен
найтись и среди элементарных $p$-групп. Первый нерассмотренный случай — группа
типа $(p,p,p)$, где $p=3$.

#theorem[
  Допустим в обозначениях @eq:abelian-group-ring-arithmetic-data, что $L$ —
  циклотомическое поле. Тогда отображение $f:G_1 (B) -> G_1 (A)$ является
  изоморфизмом и $G_1 (B) tilde.eq product_i U (A_i)$.
] <th:cyclotomic-abelian-group-ring-g1>

#proof[
  Рассмотрим коммутативную диаграмму
  $ #abelian-group-g-one-triangle() $
  Так как кольцо $B$ регулярно, то
  $ G_1 (B)=K_1 (B)=product_i K_1 (A_i)=product_i U (A_i) $
  (в силу @cor:arithmetic-special-linear-elementary). Из последнего равенства
  следует, что отображение $g_1$ (а следовательно, и отображение $f$) является
  мономорфизмом. Из @prop:abelian-k-pullback-generation вытекает, что
  отображение
  $ G_1 (B) plus.o G_1 (A slash frak(c)) -> G_1 (A) $
  сюръективно. Следовательно, достаточно показать, что образ отображения
  $G_1 (A slash frak(c)) -> G_1 (A)$ лежит в $Im (f)$. Если
  $M in italic(M) (A,frak(c))$, то модуль $M$ обладает конечной
  характеристической фильтрацией $0=M_0 subset M_1 subset dots subset M_n$, в
  которой каждый фактор $M_j slash M_(j-1)$ аннулируется некоторым
  $frak(m) in spec (A)$. Так как кольцо $A slash frak(c)$ артиново, то
  $frak(m) in maxSpec (A)$. Пусть $frak(p)$ — минимальный простой идеал кольца
  $A$, лежащий в $frak(m)$. Тогда $A slash frak(p)=A_i$ для некоторого $i$.
  Поэтому $M_j slash M_(j-1)$ является $B$-модулем. (Здесь мы воспользовались
  тем, что $L$ — циклотомическое поле, а тогда проекции $rho_i:A -> A_i$
  сюръективны.) Но если $alpha in Aut_A (M)$, то $alpha$ оставляет каждый из
  $M_j$ инвариантным и индуцирует эндоморфизм, скажем $alpha_j$, на
  $M_j slash M_(j-1)$. Тогда в группе $G_1 (A)$
  $ [M,alpha]=sum [M_j slash M_(j-1),alpha_j] in Im (f), $
  что завершает доказательство.
]

#source(477)Приведенные результаты для абелевых групп вместе с теоремой Артина
об индукции дают нам следующее утверждение для произвольных конечных групп:

#theorem[
  Пусть $pi$ — конечная группа. Рассмотрим коммутативную диаграмму
  $ #finite-group-k-one-cartan() $ <eq:finite-group-k-one-cartan>
  с точной верхней строкой (см. @cor:number-order-k1-g1-finite-generation).
  Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[$SK_1 (ZZ pi)$ — конечная группа
      экспоненты $e_(cyclicClass) (QQ,pi)^2$;]
    <cond:finite-group-ring-sk1-exponent>
    #condition-item(format: "cyrillic")[$Im (k_1)$ есть конечно порожденная
      группа ранга $(rank K_0 (RR pi)-rank K_0 (QQ pi))$, в которой экспонента
      периодической подгруппы равна $e_(cyclicClass) (QQ,pi)^2 dot e$, где
      $e=exp (pi)$ или $e=2 exp (pi)$, если число $[pi:1]$ нечетно;]
    <cond:finite-group-ring-k1-image-rank>
    #condition-item(format: "cyrillic")[коядро отображения $c_1 (ZZ pi)$
      конечно, и $Ker (g_1)$ — конечная группа экспоненты
      $e_(cyclicClass) (QQ,pi)^2$.]
    <cond:finite-group-ring-cartan-cokernel>
  ]
] <th:finite-group-ring-k1-g1>

#proof[
  Диаграмма @eq:finite-group-k-one-cartan состоит из морфизмов фробениусовых
  модулей над фробениусовым функтором $G_ZZ$. Следовательно, все оценки
  экспонент вытекают из @prop:induction-exponent-module-bound и
  @prop:induction-exponent-dedekind-ring, как только они будут установлены для
  циклической группы $pi$.

  Если группа $pi$ циклическая, то $SK_1 (ZZ pi)=0$ (см.
  @prop:cyclic-sylow-group-ring-sk1-torsion-free), и отображение $g_1$
  инъективно (это следует непосредственно из
  @th:cyclotomic-abelian-group-ring-g1). Кроме того, в силу
  @th:abelian-group-ring-units@cond:higman-group-ring-torsion-units группа
  $Im (k_1)$ содержит периодическую подгруппу $plus.minus pi$ в том случае,
  когда группа $pi$ циклическая. Формула для ранга группы $K_1 (ZZ pi)$ вытекает
  из @th:arithmetic-k1-finiteness@cond:arithmetic-relative-k1-free-rank в общем
  случае. Тем самым установлено все, кроме конечности группы
  $Coker (c_1 (ZZ pi))$, но это следует из
  @th:arithmetic-k1-finiteness@cond:arithmetic-cartan-k1-cokernel-finite.
]
