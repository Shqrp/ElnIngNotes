#import "@preview/theorion:0.3.3": *
#import math: *

#import cosmos.rainbow: *

#show: show-theorion

#set text(lang: "it")
#set page(numbering: "I", footer: [], header: context {
  if counter(page).display() != "I" {
    if calc.even(counter(page).get().at(0)) {
      align(left, [#{ counter(page).display() } - _Analisi Matematica I_])
    } else {
      align(right, [_Analisi Matematica I_ - #{ counter(page).display() }])
    }
  }
})

#align(center, heading(outlined: false, [Analisi Matematica I]))
#align(
  center,
  [Andrea Giurgola - Prof. Fabio Punzo \ Ingegneria Elettronica, Politecnico di Milano],
) \

#set heading(numbering: "1.1.")
#set-theorion-numbering("1.1")
#outline(title: [Indice])

#pagebreak()
#counter(page).update(1)
#set page(numbering: "1")

= Richiamo di logica

La logica si basa su *predicati* (o *affermazioni*), i quali possono essere veri o falsi e si connettono tra loro tramite connettivi:
- *Implicazione logica* ($=>$): se l'antecedente è vero allora anche il conseguente sarà vero, ma non vale il contrario
- *Equivalenza logica* ($<=>$): la verità di uno dei due predicati implica la verità dell'altro e viceversa
- *Contrapposizione*: data un'implicazione ($p => q$) allora sarà anche vero l'implicazione di senso inverso degli opposti dei due predicati (se $p => q$, allora anche $overline(q) => overline(p)$)

Alla base della matematica esiste il *teorema*, ossia un'implicazione logica in cui l'antecedente si dice *ipotesi* e il conseguente si dice *tesi*. La *dimostrazione* è una catena di passaggi logici che giustifica tale implicazione. Esistono tre tipi di dimostrazioni:
- *Diretta*: viene dimostrato che l'ipotesi implica la tesi
- *Indiretta per contrapposizione*: viene dimostrato che l'inverso della tesi implica l'inverso dell'ipotesi
- *Indiretta per assurdo*: viene dimostrato che la negazione della tesi porta ad un risultato falso, rendendo dunque vera la tesi
- *Per induzione*: un tipo di dimostrazione che vale solo all'interno dei numeri naturali

Esistono tre quattro diverse tipologie di teorema:
- *Lemma*: un teorema di piccola importanza
- *Proposizione*: un teorema di media importanza
- *Teorema*
- *Corollario*: l'insieme di conseguenze di un teorema

== Il principio di induzione

Il *principio di induzione* è un principio dimostrativo che permette di dimostrare un teorema in $NN$ riducendo notevolmente il numero di passaggi necessari. \
Sia $p(n)$ una proposizione logica che dipende dalla variabile $n in NN$. Se $p(n)$ è valida per $n = 0$ (*ipotesi* o *base induttiva*), allora sarà vera anche per $n = 0 + 1$ (*passo induttivo*), e così via. Secondo il principio di induzione, allora $p(n)$ è vera $forall n in NN$. Di seguito tre esempi di teoremi dimostrabili con il principio di induzione.

#theorem(
  title: [Somma dei primi $n$-naturali],
  $ sum^n_(k=1)k = n/2(n+1), forall x in NN $,
)
#proof([
  Sia $p(n)$ la suddetta relazione. \
  $p(0)$: $0 = 0/2(0+1), 0 = 0$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $1 + 2 + 3 + ... + n + (n + 1) = (n + 1)/2[(n + 1) + 1]$ \
  Riscrivendo la somma fino a $n$ come $p(n)$ \
  $(1 + 2 + 3 + ... + n) + (n + 1) = n/2(n + 1) + (n + 1) = (n + 1)(n/2 + 1) = (n + 1)((n + 2)/2) = (n + 1)/2(n + 1 + 1)$. \ In quanto si è ritornati alla scrittura di $p(n + 1)$, allora è verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, il teorema vale $forall n in NN$.
]) \ \

#theorem(title: [Disuguaglianza di Bernoulli], [
  Sia $h in RR, h > -1$. Pertanto $(1+h)^n >= 1 + n h$.
])
#proof([
  Sia $p(n)$ la suddetta disuguaglianza. \
  $p(0)$: $(1 + h)^0 >= 1 + 0, 1 >= 1$. Pertanto $p(0)$ è verificata.\
  $p(n + 1)$: $(1 + h)^(n + 1) >= 1 + (n + 1)h$ \
  $(1 + h)^(n + 1) = (1 + h)^n (1 + h)$. Si nota che $1 + h > 0$ e che $(1 + h)^n >= (1 + n h)$. Dunque \
  $(1 + h)^n (1 + h) >= (1 + n h)(1 + h) = n h^2 + n h + h + 1$. Dunque \
  $(1 + h)^(n + 1) >= n h^2 + n h + h + 1$. $n h^2$ si può non considerare in quanto rende solo più forte la relazione di disuguaglianza. Dunque \
  $(1 + h)^(n + 1) >= n h + h + 1, (1 + h)^(n + 1) >= 1 + (n + 1)h$. \
  È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

#proposition(
  title: [Somma della progressione geometrica],
  [
    Sia $q in RR, q != 1$. $sum^n_(k = 0)q^k = (1 - q^(n + 1))/(1 - q), forall n in NN$
  ],
)
#proof([
  #set par(leading: 1.065em)
  Sia $p(n)$ la suddetta proposizione. \
  $p(0)$: $q^0 = (1 - q^1)/(1 - q), 1 = cancel(1 - q)/cancel(1 - q), 1 = 1$. Pertanto $p(0)$ è vera. \
  $p(n + 1)$: $sum^(n + 1)_(k = 0)q^k = (1 - q^(n + 2))/(1 - q), sum^(n + 1)_(k = 0)q^k = sum^(n)_(k = 0)q^k + q^(n + 1) = (1 - q^(n + 1))/(1 - q) + q^(n + 1) =$ \
  $= (1 - cancel(q^(n + 1)) + cancel(q^(n + 1)) - q^(n + 2))/(1 - q) = (1 - q^(n + 2))/(1 - q)$. \ È verificato che $p(n) => p(n + 1)$, dunque, per il principio di induzione, $p(n)$ è vera $forall n in NN$.
])

= I numeri

Tra gli insiemi numerici di base si possono annoverare i seguenti:
- *Numeri naturali*: comprende tutti i numeri interi positivi maggiori o uguali a 0
$ NN := {0,1,2,3,...} $
- *Numeri interi relativi*: comprende tutti i numeri interi positivi e negativi
$ ZZ := {..., -2, -1, 0, 1, 2, ...} $
- *Numeri razionali*: comprende tutti i numeri esprimibili come rapporto tra due interi
$ QQ := { m/n : m,n in italic(ZZ), n != 0 } $

Quindi, in sintesi, $NN subset ZZ subset QQ$. \ \

== I numeri razionali

Due frazioni $a/b$ e $c/d$ si dicono *equivalenti* se vale la relazione $a d = b c$. \

I numeri razionali possono anche essere rappresentati sotto forma di *allineamento decimale* (per esempio $1/2 = 0,5$). Un numero razionale può essere:
- *finito*: la parte decimale ha un numero limitato di cifre
- *periodico*: la parte decimale si ripete all'infinito con costanza

#note-box([Gli allineamenti decimali con periodo $9$ non provengono da alcuna divisione (ad esempio $0.overline(9) = 1$).])

#definition([
  + $n in ZZ$ si dice _pari_ se $exists h in ZZ : n = 2h$
  + $n in ZZ$ si dice _dispari_ se $exists h in ZZ : n = 2h + 1$
]) <raz:defpari>
#proposition(
  title: [Parità dei quadrati],
  [$n$ pari $=> n^2$ pari, $n$ dispari $=> n^2$ dispari],
) <raz:pdq>
#proof([\ Sia $n in ZZ$. $n$ è pari $<=> exists h in ZZ : n = 2h$. Dunque \
  $n^2 = (2h)^2 = 4h^2 = 2(2h^2) = 2k$, essendo $k = 2h^2 in ZZ$. \
  Dunque $n^2$ è pari \ \
  Sia $n in ZZ$. $n$ è dispari $<=> exists h in ZZ : n = 2h + 1$. Dunque \
  $n^2 = (2h +1)^2 = 4h^2 + 4h + 1 = 2(2h^2 +2h) + 1 = 2k + 1$ dove $k = 2h^2 + 2h$. \
  Dunque $n^2$ è dispari
])
#proposition(
  title: [Parità dei quadrati inversa],
  [$n^2$ pari $=> n$ pari, $n^2$ dispari $=> n$ dispari],
) <raz:pdq2>
#proof([Sia $n in ZZ$. Introducendo i predicati $cal(P)$: $n$ è dispari e $cal(Q)$: $n^2$ è dispari, dalla @raz:pdq si inferisce che $cal(P) => cal(Q)$. Poiché la negazione di dispari è pari, allora, per contrapposizione, è vero che $overline(cal(Q)) => overline(cal(P))$. ])

=== Il problema delle radici

I numeri razionali presentano lacune in materia di estrazione di radici.
#definition([Sia $a >= 0$. Si dice _radice quadrata_ di $a$ un numero $b$ tale che $b^2 = a, b >= 0$.])
#theorem(
  title: [Irrazionalità di $sqrt(2)$],
  [$sqrt(2)$ non è un numero razionale.],
)
#proof([
  Supponiamo, per assurdo, che $sqrt(2) in QQ$. Dunque \
  $sqrt(2) = m/n$ essendo $m,n in ZZ, n != 0, m, n$ primi tra loro. Elevando al quadrato: \
  $2 = m^2/n^2 => m^2 = 2n^2$. Pertanto $m^2$ è pari e anche $m$ è pari. Dunque $exists k in Z : m = 2k$ \
  $2n^2 = m^2 = (2k)^2 = 4k^2 => 2n^2 = 4k^2 => n^2 = 2k^2$. Pertanto $n^2$ è pari, quindi anche $n$ è pari. \
  Questo è un assurdo, dal momento che $m$ e $n$ sono per definizione primi tra loro, quindi non possono essere entrambi pari.
]) \ \

== I numeri reali

L'insieme dei numeri reali rappresenta quell'insieme numerico che comprende *tutti gli allineamenti decimali finiti*,* infiniti periodici* e *infiniti non periodici*. Dunque:
$ NN subset ZZ subset QQ subset RR $

Tutti quei numeri reali che non sono razionali si dicono *numeri irrazionali*, i quali appartengono all'insieme $RR backslash QQ$.

=== La rappresentazione geometria di $RR$

Se si rappresentano i numeri razionali sulla retta, ci saranno sempre dei buchi (per es. ($sqrt(2) in RR$ ma $in.not QQ$). Invece i numeri reali, in quanto comprendono anche i non razionali, godono della *proprietà di continuità* (o *completezza*) *dei numeri reali*.
\
== Estremo superiore ed inferiore

#definition([
  #set par(leading: 1.06em)
  Sia $E subset.eq RR$. \
  + $M in RR$ si dice _massimo_ ($max E$) di E se $cases(M in E, M >= x\, forall x in E)$ \
  + $m in RR$ si dice _minimo_ ($min E$) di E se $cases(m in E, m <= x\,forall x in E)$
])
#example([$E = (0; 2] => max E = 2, exists.not min E$, $E = [0; 2) => exists.not max E, min E = 0$])
#definition([
  Sia $E subset.eq RR$ \
  + $Lambda in RR$ si dice _maggiorante_ di E se $Lambda >= x, forall x in E$ \
  + $lambda in RR$ si dice _minorante_ di E se $lambda <= x, forall x in E$
])
#definition([Sia $E subset.eq RR, E != emptyset$.
  + Si dice _estremo superiore_ ($sup E$) di E il minimo dei maggioranti
  + Si dice _estremo inferiore_ ($inf E$) di E il massimo dei minoranti.
])
#example($E = (0; 2] => sup E = 2 = max E, inf E = 0$)
#note-box([Se $exists max E$ allora coincide con $sup E$.])

L'estremo superiore è caratterizzato da due proprietà:
- $sup E$ è un maggiorante di E: $sup E >= x, forall x in E$
- Qualunque numero $< sup E$ non è un maggiorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon > sup E - epsilon$
L'estremo inferiore di E è caratterizzato da:
- $inf E$ è minorante di E: $inf E <= x, forall x in E$
- Qualunque numero $> inf E$ non è minorante di E: $forall epsilon > 0 #" " exists x_epsilon in E : x_epsilon < inf E + epsilon$
\
#definition([
  + $E$ si dice _limitato superiormente_ se ammette almeno un maggiorante ($exists Lambda in RR, Lambda >= x, forall x in E$)
  + $E$ si dice _limitato inferiormente_ se ammette almeno un minorante ($exists lambda in RR, lambda <= x, forall x in E$)
  + $E$ si dice _limitato_ se lo è sia inferiormente che superiormente ($exists Lambda, lambda in RR : lambda <= x <= Lambda, forall x in E$)
])
#note-box([
  + $E$ non è limitato superiormente $<=> exists x in E : x >= Lambda, forall Lambda in RR => sup E = +infinity$
  + $E$ non è limitato inferiormente $<=> exists x in E : x <= lambda, forall lambda in RR => inf E = -infinity$
])
#theorem(
  title: [Proprietà di continuità/completezza di $RR$],
  [
    Un insieme $E subset.eq RR != emptyset$ limitato superiormente ha sempre un $sup E$ in $RR$. Analogamente, un insieme $E$ limitato inferiormente ha sempre un $inf E$ in $RR$.
  ],
) <esi:pcrr>
#corollary([
  Se $E subset.eq RR != emptyset$, allora $exists sup E, inf E in RR$
])
#example([
  Sia $A = { x in QQ : x^2 <= 2 } subset.eq QQ subset.eq RR => sup A = sqrt(2)$ \
  In questo caso l'estremo superiore appartiene a $RR$ ma non a $QQ$, dunque osserviamo che in $QQ$ la proprietà di completezza è falsa. \
])

== Potenze e radici

Grazie alla proprietà di continuità di $RR$ vale il seguente teorema.
#theorem(
  title: [Radice $n$-esima di un numero],
  [
    Sia $n in NN, y in RR : n >= 1, y > 0$. Allora $exists x in RR : x^n = y$, dove $x$ si dice la _radice $n$-esima_ di $y$.
  ],
)

Siano $r = m/n, a > 0$, con $m in ZZ, n in NN, n != 0$. Allora si può dire che
$ a^r := (a^m)^(1/n) = root(n, a^m) $
Inoltre, se $n$ è dispari, vale anche la seguente relazione.
$ (-a)^r = -root(n, a^m) $
Ora siano $a > 0, b in RR$. $a^b$ rappresenta una *potenza ad esponente reale*. Dunque
$
  a > 1 <=> a^b := sup {a^r : r in QQ, r <= b} \
  a < 1 <=> a^b := sup {a^r : r in QQ, r >= b}
$
In altre parole, se consideriamo la potenza $a^b$ per un qualsiasi numero reale $b$, essa rappresenta l'estremo superiore dell'insieme delle potenze di $a$. Nel caso $a > 1$, gli esponenti delle potenze nell'insieme sono tutti minori o uguali di $b$, mentre nel caso $a < 1$, essi sono tutti maggiori di $b$.

#theorem(
  title: [Logaritmo di un numero in base $a$],
  [
    Siano $a > 0, a != 1, y > 0$. Allora $exists x in RR : a^x = y$ dove $x$ è detto il _logaritmo di $y$ in base $a$_.
  ],
)

== Valore assoluto

#definition(
  title: [Valore assoluto],
  [
    Si dice _valore assoluto_ o _modulo_ di un numero $x in RR$ \
    $ abs(x) := cases(x"   se" x >= 0, -x" se" x < 0) $
  ],
)
#warning-box([Sia $a in RR$. Allora $sqrt(a^2) = abs(a)$ poiché il risultato di una radice di ordine pari è sempre positivo.])

In altre parole, $abs(a) = max{a, -a} <=> abs(a) = abs(-a), a <= abs(a), -a <= abs(a)$.

#theorem(title: [Disuguaglianza triangolare], [
  $abs(a + b) <= abs(a) + abs(b), forall a, b in RR$.
])
#proof([
  Siano $a, b in RR$. \
  Sapendo che $a <= abs(a)$ e $b <= abs(b)$ e che $-a <= abs(a)$ e $-b <= abs(b)$ e sommando membro a membro si ha \
  $a + b <= abs(a) + abs(b), -a -b <= abs(a) + abs(b)$ \
  In virtù del fatto che $abs(a) = max{a, -a}$ allora $abs(a + b) = max{a + b, -a - b} <= abs(a) + abs(b)$.
])

Analogamente, è vera anche la relazione $abs(abs(a) - abs(b)) <= abs(a + b), forall a, b in RR$.

#pagebreak()
#outline(title: [Indice dei teoremi e dimostrazioni], target: figure.where(
  kind: "theorem",
))
