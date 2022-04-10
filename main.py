const = [] # a - e
forms = []
neg = [chr(172), '~', "NOT"]
kon = ["AND", '∧', '&']
alt = ["OR", '∨', '|']
imp = ["IMPLIES",'→', "IMP"]
row = ["IFF", '↔']
xor = ["XOR", '⊕']
ogl = ["FORALL", '∀']
egz = ["EXISTS", '∃']
#print(ord("¬"))
def glab(form, ile = 1, glebokosc = 0, zwroc = [["UWU"]]):
	if ile == 0:
		return
	i = form[len(form) - 1]
	kt = len(form) - 1
	nr = int(ord(i[:1]))
	if (nr >= ord("a") and nr <= ord("e")) or (nr >= ord("A") and nr <= ord("Z")) and len(i) == 1:
			zwroc.append(i)
			form.pop(kt)
			glab(form, ile - 1, glebokosc + 1, zwroc)
	else:
		if i in neg:
			if zwroc[len(zwroc)-1] not in neg:
				zwroc.append(i)
				form.pop(kt)
			else:
				zwroc.pop(len(zwroc)-1)
				form.pop(kt)
			glab(form, 1, glebokosc + 1, zwroc)
		else:
			nr = int(ord(i[0]))
			if nr >= ord("f") and nr <= ord("v"):
				zwroc.append(form[kt])
				form.pop(kt)
				kt -= 1
				for g in range(int(i[2:])):
					glab(form, int(i[2:]), glebokosc + 1, zwroc)
			else:
				zwroc.append(i)
				form.pop(kt)
				glab(form, 1, glebokosc + 1, zwroc)
				glab(form, 1, glebokosc + 1, zwroc)
	if glebokosc == 0:
		return zwroc[1:], form
def MTS(formulas, kopia = [], uzyte = []):
	#print(formulas)
	#szukanie komplementarnych
	if formulas == kopia:
		return False
	kopia = formulas.copy()
	for i in range(len(formulas)):
		for j in range(i+1, len(formulas)):
			if formulas[i] == formulas[j][0:len(formulas[j])-1] or formulas[j] == formulas[i][0:len(formulas[i])-1]:
				return False
	for i in formulas:
		uzyte.append([])
		ktora = formulas.index(i)
		#formula typu alfa
		if i[len(i) - 1] in kon:
			nowy1 = []
			t, r = glab(i[:len(i)-1], 1, 0, ["UWU"])
			for g in range(len(t)-1, -1, -1):
				nowy1.append(t[g])
			formulas.append(nowy1)
			formulas.append(r)
			formulas.pop(ktora)
			uzyte[ktora] = []
			return MTS(formulas, kopia, uzyte)
		elif i[len(i) - 1] in neg and i[len(i) - 2] in alt:
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			if nowy1[len(nowy1)-1] == "NOT":
				nowy1.pop(len(nowy1)-1)
			else:
				nowy1.append("NOT")
			formulas.append(nowy1)
			if r[len(r) - 1] == "NOT":
				r.pop(len(r) - 1)
			else:
				r.append("NOT")
			formulas.append(r)
			formulas.pop(ktora)
			uzyte[ktora] = []
			return MTS(formulas, kopia, uzyte)
		elif i[len(i) - 1] in neg and  i[len(i) - 2] in imp :
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.append(r)
			if nowy1[len(nowy1) - 1] == "NOT":
				nowy1.pop(len(nowy1) - 1)
			else:
				nowy1.append("NOT")
			formulas.append(nowy1)
			formulas.pop(ktora)
			uzyte[ktora] = []
			return MTS(formulas, kopia, uzyte)
		elif i[len(i) - 1] in neg and (i[len(i) - 2] in xor ):
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.append(r + nowy1 + ["IMPLIES"])
			formulas.append(nowy1 + r + ["IMPLIES"])
			formulas.pop(ktora)
			uzyte[ktora] = []
			return MTS(formulas, kopia, uzyte)
		elif i[len(i) - 1] in row:
			nowy1 = []
			t, r = glab(i[:len(i) - 1], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.append(r + nowy1 + ["IMPLIES"])
			formulas.append(nowy1 + r + ["IMPLIES"])
			formulas.pop(ktora)
			uzyte[ktora] = []
			return MTS(formulas, kopia, uzyte)

		#formula typu beta
		elif i[len(i) - 1] in alt:
			nowy1 = []
			t, r = glab(i[:len(i) - 1], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.pop(ktora)
			uzyte[ktora] = []
			formulas.append(nowy1)
			formu = formulas.copy()
			F1 = MTS(formulas, kopia, uzyte)
			formulas = formu.copy()
			formulas.append(r)
			uzyte[ktora] = []
			F2 = MTS(formulas, kopia, uzyte)
			return F1 or F2
		elif i[len(i) - 1] in xor:
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1, 0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.pop(ktora)
			uzyte[ktora] = []
			formu = formulas.copy()
			formulas.append(r + nowy1 + ["IMPLIES", "NOT"])
			F1 = MTS(formulas, kopia, uzyte)
			formulas = formu.copy()
			formulas.append(nowy1 + r + ["IMPLIES", "NOT"])
			uzyte[ktora] = []
			F2 = MTS(formulas, kopia, uzyte)
			return F1 or F2
		elif i[len(i) - 1] in neg and i[len(i) - 2] in row:
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.pop(ktora)
			uzyte[ktora] = []
			formu =formulas.copy()
			formulas.append(r + nowy1 + ["IMPLIES", "NOT"])
			F1 = MTS(formulas, kopia, uzyte)
			formulas = formu.copy()
			formulas.append(nowy1 + r + ["IMPLIES", "NOT"])
			uzyte[ktora] = []
			F2 = MTS(formulas, kopia,uzyte)
			return F1 or F2
		elif i[len(i) - 1] in neg and i[len(i) - 2] in kon:
			nowy1 = []
			t, r = glab(i[:len(i) - 2], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.pop(ktora)
			uzyte[ktora] = []
			if nowy1[len(nowy1)-1] == "NOT":
				nowy1.pop(len(nowy1)-1)
			else:
				nowy1.append("NOT")
			if r[len(nowy1) - 1] == "NOT":
				r.pop(len(nowy1) - 1)
			else:
				r.append("NOT")
			formu = formulas.copy()
			formulas.append(nowy1)
			F1 = MTS(formulas, kopia, uzyte)
			formulas = formu.copy()
			formulas.append(r)
			uzyte[ktora] = []
			F2 = MTS(formulas, kopia, uzyte)
			return F1 or F2
		elif i[len(i) - 1] in imp:
			nowy1 = []
			t, r = glab(i[:len(i) - 1], 1,0, ["UWU"])
			for g in range(len(t) - 1, -1, -1):
				nowy1.append(t[g])
			formulas.pop(ktora)
			uzyte[ktora] = []
			if r[len(r)-1] == "NOT":
				r.pop(len(r)-1)
			else:
				r.append("NOT")
			formu = formulas.copy()
			formulas.append(nowy1)
			F1 = MTS(formulas, kopia, uzyte)
			formulas = formu.copy()
			formulas.append(r)
			uzyte[ktora] = []
			F2 = MTS(formulas, kopia, uzyte)
			return F1 or F2
		#formua typu delta
		elif i[len(i)-1] in egz:
			st = const[len(const)-1]
			st = chr(ord(st)+1)
			const.append(st)
			zmienna = i[0]
			nowy = []
			for k in i[1:len(i)-1]:
				if k == zmienna:
					nowy.append(st)
				else:
					nowy.append(k)
			formulas.pop(formulas.index(i))
			formulas.append(nowy)
			return MTS(formulas, kopia, uzyte)
		elif i[len(i)-1] in neg and i[len(i) - 2] in ogl:
			st = const[len(const)-1]
			st = chr(ord(st)+1)
			const.append(st)
			zmienna = i[0]
			nowy = []
			for k in i[1:len(i)-2]:
				if k == zmienna:
					nowy.append(st)
				else:
					nowy.append(k)
			nowy.append("NOT")
			formulas.append(nowy)
			formulas.pop(formulas.index(i))
			return MTS(formulas, kopia, uzyte)

		#formula typu gamma
		elif i[len(i) - 1] in ogl:
			zmienna = i[0]
			for stala in const:
				nowy = []
				if stala in uzyte[ktora]:
					continue
				uzyte[ktora].append(stala)
				for j in range(1, len(i)-1):
					if i[j] == zmienna:
						nowy.append(stala)
					else:
						nowy.append(i[j])
				formulas.append(nowy)
				return MTS(formulas, kopia, uzyte)
		elif i[len(i) - 1] in neg and i[len(i) - 2] in egz:
			zmienna = i[0]
			for stala in const:
				nowy = []
				if stala in uzyte[ktora]:
					continue
				uzyte[ktora].append(stala)
				for j in range(1, len(i) - 2):
					if i[j] == zmienna:
						nowy.append(stala)
					else:
						nowy.append(i[j])
				nowy.append("NOT")
				formulas.append(nowy)
				return MTS(formulas, kopia, uzyte)
	#lisc otwarty
	return True
while(1):
	try:
		czy = 0
		form = input().split(" ")
		forms.append(form)
		for i in form:
			i = i[0]
			if ord(i) >= ord("a") and ord(i) <= ord("e"):
				if i in const:
					continue
				const.append(i)
		if const == []:
			const.append("a")
		if MTS(forms) == False:
			print("NIESPEŁNIALNA")
		else:
			print("SPEŁNIALNA")
		stale=[]
		forms =[]
	except(EOFError):
		break
