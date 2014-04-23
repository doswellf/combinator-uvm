#
# SimVision Command Script
#


#
# preferences
#
simvision -submit preferences set toolbar-Windows-WatchList {
  usual
  hide icheck
}

#
# groups
#
simvision -submit {
  catch {group new -name {apb IF} -overlay 0}

  group using {apb IF}
  group set -overlay 0
  group set -comment {}
  group set -parents {}
  group set -groups {}
  group clear 0 end

  group insert \
    demo_top.apb_if_0.pclock \
    demo_top.apb_if_0.preset \
    demo_top.apb_if_0.penable \
    demo_top.apb_if_0.pready \
    demo_top.apb_if_0.paddr \
    demo_top.apb_if_0.pwdata \
    demo_top.apb_if_0.prdata \
    demo_top.apb_if_0.prwd \
    demo_top.apb_if_0.psel \
    demo_top.apb_if_0.pslverr \
    demo_top.apb_if_0.ua_int

}

#
# cursors
#
simvision -submit {
  set time 0
  if {[catch {cursor new -name  TimeA -time $time}] != ""} {
    cursor set -using TimeA -time $time
  }
}

#
# mmaps
#
simvision -submit {

  mmap new -reuse -name {Boolean as Logic} -contents {
    {%c=FALSE -edgepriority 1 -shape low}
    {%c=TRUE -edgepriority 1 -shape high}
  }
  mmap new -reuse -name {Example Map} -contents {
    {%b=11???? -bgcolor orange -label REG:%x -linecolor yellow -shape bus}
    {%x=1F -bgcolor red -label ERROR -linecolor white -shape EVENT}
    {%x=2C -bgcolor red -label ERROR -linecolor white -shape EVENT}
    {%x=* -label %x -linecolor gray -shape bus}
  }
}

#
# Design Browser windows
#
simvision -submit {
   window target "Design Browser 1" on
   browser using {Design Browser 1}
   browser set \
    -scope demo_top.apb_if_0
   browser yview see demo_top.apb_if_0
   browser timecontrol set -lock 0
}

#
# Waveform windows
#
simvision -submit {
   if {[catch {window new WaveWindow -name "Waveform 1" -geometry 1120x799+-6+0}] != ""} {
      window geometry "Waveform 1" 1120x799+-6+0
   }
   window target "Waveform 1" on
   waveform using {Waveform 1}
   waveform sidebar visibility partial
   waveform set \
     -primarycursor TimeA \
     -signalnames name \
     -signalwidth 175 \
     -units ns \
     -valuewidth 75
   cursor set -using TimeA -time 0
   waveform baseline set -time 260ns
   waveform xview limits 0ns 400ns
}

simvision -submit {set groupId [waveform add -groups {{apb IF}}]}
