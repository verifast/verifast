revrelease:
	set VFVERSION=r$(REVISION)
	rmdir /s /q exportdir
	svn export $(VERIFAST_REPOSITORY_URL)@$(REVISION) exportdir
	cd exportdir
	cd src
	nmake release
	del ..\..\verifast-r$(REVISION).zip
	7z a ..\..\verifast-r$(REVISION).zip verifast-r$(REVISION)

release:
	set VFVERSION=$(VERSION)
	svn export $(VERIFAST_REPOSITORY_URL)/release.mak release-latest.mak
	nmake /f release-latest.mak CALLER=Makefile
