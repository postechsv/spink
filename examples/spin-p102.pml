chan ch[1] = [1] of { int }

active proctype A() { ch[0] ! 1 }
active proctype B() { ch[0] ! 2 }
active proctype C()
{	if
	:: ch[0] ? 1
	:: ch[0] ? 2
	fi
}
