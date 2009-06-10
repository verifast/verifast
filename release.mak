!if "$(CALLER)" != "Makefile"
!	error "Please call this makefile only via Makefile"
!endif

!if "$(VFVERSION)" == "3.1"
REVISION=74
!elseif "$(VFVERSION)" == "4.0"
REVISION=94
!elseif "$(VFVERSION)" == "4.0.1"
REVISION=97
!elseif "$(VFVERSION)" == "4.0.2"
REVISION=100
!elseif "$(VFVERSION)" == "5.0"
REVISION=120
!elseif "$(VFVERSION)" == "5.1"
REVISION=125
!elseif "$(VFVERSION)" == "5.1.1"
REVISION=130
!elseif "$(VFVERSION)" == "6.0"
REVISION=168
!elseif "$(VFVERSION)" == "7.0"
REVISION=192
!else
!	error "Environment variable VFVERSION has invalid value: Unknown release name '$(VFVERSION)'"
!endif

release:
	-rmdir /s /q exportdir
	svn export $(VERIFAST_REPOSITORY_URL)@$(REVISION) exportdir
	cd exportdir
	cd src
	nmake release
	-del ..\..\verifast-$(VFVERSION).zip
	7z a ..\..\verifast-$(VFVERSION).zip verifast-$(VFVERSION)
