@echo off
setlocal
set PASSED=0
set FAILED=0

pushd unit-tests
FOR /f "tokens=*" %%G IN ('dir /b *.js') DO (
    echo %%~fG
    
    set fname=%%~fG
    
    ..\..\bin\jstest.exe ..\json_print.js -args %%G > %%G.ast
    ocamlrun ..\..\obj\s5.d.byte -set-json ..\..\src\c3desugar.bat ^
      -c3-js %%G.ast -js-to-s5 ^
      -env ..\..\envs\es5.env -apply ^
      -eval | find "passed" > NUL

    if ERRORLEVEL 1 (
	echo Failed
	set /A FAILED+=1
    ) else (
        echo Passed
	set /A PASSED+=1
	del %%G.ast
    )

    echo.
)
popd

echo "%PASSED% tests passed"
echo "%FAILED% tests failed"
