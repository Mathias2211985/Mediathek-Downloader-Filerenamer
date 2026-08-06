# Mediathek Downloader

Ein Desktop-Programm für die deutschen öffentlich-rechtlichen Mediatheken:
suchen, herunterladen, automatisch auf neue Folgen prüfen — und die Dateien
anschließend so benennen und einsortieren, dass Plex sie sauber erkennt.

Ein einzelnes Python-Skript mit Tkinter-Oberfläche, keine Installation nötig.

---

## Was es kann

### Suchen und herunterladen
- Durchsucht **MediathekViewWeb** sowie die APIs von **ARD** und **ZDF**
- Filter nach Sender, Sprache, Dauer; Barrierefreiheits-Fassungen ausblendbar
- Zeigt an, welche Treffer **Duplikate** sind und welche du **schon hast**
- Download-Warteschlange mit Pause, Abbruch, Wiederholung und Umsortieren
- Optionales **Tempolimit** und Zeitfenster (z. B. tagsüber gedrosselt)

### Watchlist
- Sendungen dauerhaft beobachten, neue Folgen werden automatisch geladen
- Zeitplan pro Eintrag — auch **mehrere Uhrzeiten am Tag** (`08:00, 14:00, 22:00`)
- Merkt sich per Hash, was bereits geladen wurde

### Umbenennen
Serien über **TheTVDB**, **Trakt.tv** oder **TVmaze**, Filme über
**TheMovieDB** oder **OMDb**.

- **Mehrere Serien in einem Durchgang.** Ein gemischter Ordner wird nach
  Serien gruppiert; jede Gruppe wird einzeln aufgelöst. Unklare Gruppen
  blockieren die fertigen nicht.
- **Es wird nie geraten.** Liefert die Datenbank mehrere gleich gute Treffer
  (bei TheTVDB heißen z. B. drei Serien exakt „Victoria"), bleibt die Gruppe
  stehen und fragt nach, statt eine auszuwürfeln. Die einmal bestätigte Wahl
  wird gemerkt.
- Der Serienname wird aus dem Dateinamen gelesen — und wenn er dort fehlt,
  aus dem **Ordnernamen** (Staffel-Ordner und Release-Kürzel werden dabei
  abgeschnitten).
- **Einzelne Folge korrigieren:** Staffel/Folge eintippen oder einen Titel
  suchen, auch bei bereits (falsch) zugeordneten Zeilen.
- **Sample-Dateien** aus Scene-Releases werden übersprungen.
- Die **Dateiendung der Quelldatei** bleibt erhalten — eine `.mkv` wird nicht
  zur `.mp4`.

### Einsortieren
- **Serien:** `<Ziel>/<Serie>/Staffel 01/…`, Staffelformat frei wählbar
- **Filme:** eigener Zielordner, optional gruppiert nach **Anfangsbuchstabe**,
  **Jahrzehnt** oder **Jahr**, optional ein eigener Ordner je Film
- **Plex-IDs:** Serienordner können `{tvdb-12345}` tragen, damit Plex die
  Serie eindeutig erkennt
- **Serien-Aliase:** frei wählbarer Ordnername je Serie
  (`Hubert ohne Staller` → `Hubert & Staller`)
- **Untertitel und Begleitdateien** (`.srt`, `.ass`, `.idx`, `.nfo`) wandern mit
- **Aufräumen:** leer gewordene Quellordner werden entfernt, abgearbeitete
  Release-Ordner komplett — nie jedoch der gewählte Ordner oder ein Ordner,
  in dem noch eine echte Videodatei liegt
- **Bei vorhandener Zieldatei** wird gefragt: überschreiben, neue löschen oder
  überspringen (mit Größenvergleich und „für alle übernehmen")

### Ordner-Scanner
Feste Ordner für Serien und Filme hinterlegen und auf Knopfdruck einlesen —
inklusive Unterordner, ohne Samples, ohne Doppelte.

---

## Installation

Voraussetzung ist **Python 3.10 oder neuer**.

```bash
pip install requests tkinterdnd2 pillow
python mediathek_downloader.py
```

| Paket | wofür | nötig? |
|---|---|---|
| `requests` | alle API-Zugriffe | **ja** |
| `tkinterdnd2` | Dateien per Drag & Drop | optional |
| `pillow` | Filmposter in der Auswahl | optional |
| `ffprobe` | echte Auflösung statt Schätzung | optional |

Ohne die optionalen Pakete startet das Programm trotzdem, die jeweilige
Funktion fehlt dann einfach.

---

## API-Schlüssel

Alle Schlüssel sind kostenlos und werden nur für das Umbenennen gebraucht —
Suchen und Herunterladen funktionieren ohne.

| Dienst | wofür | woher |
|---|---|---|
| TheTVDB | Serien (empfohlen) | thetvdb.com → Account → API Access |
| TheMovieDB | Filme | themoviedb.org → Einstellungen → API |
| Trakt.tv | Serien, Alternative | trakt.tv → Settings → Your API Apps |
| OMDb | Filme, Alternative | omdbapi.com/apikey.aspx |
| **TVmaze** | Serien | **kein Schlüssel nötig** |

Einzutragen unter **Umbenennen → ⚙ API & Format**.

> **TVmaze** liefert Episodentitel in der Originalsprache der Serie. Bei
> deutschen Produktionen sind sie damit deutsch, bei synchronisierten
> Auslandsserien nicht. Die `{tvdb-…}`-ID im Ordnernamen gibt es nur mit
> TheTVDB als Quelle.

---

## Konfiguration

Alle Einstellungen liegen in `watchlist.json` neben dem Programm. Die Datei
enthält **deine API-Schlüssel und deine Ordnerpfade** und gehört deshalb nicht
in ein öffentliches Repository — die mitgelieferte `.gitignore` schließt sie aus.

Zum Start kannst du `watchlist.example.json` nach `watchlist.json` kopieren.

---

## Bedienung in Kurzform

1. **Suche** — Sendung im Feld *Sendung / Thema* eintragen (nicht unter *Titel*,
   dort steht der Folgentitel). Treffer ankreuzen, herunterladen.
2. **Watchlist** — Sendung eintragen, Zeitplan setzen, fertig.
3. **Umbenennen** — Dateien hineinziehen oder *Scan-Ordner einlesen*. Das
   Programm gruppiert nach Serie und ordnet zu. Gelbe Gruppen brauchen deine
   Entscheidung. Dann *Alle umbenennen*.

Die Statuszeile sagt jeweils, was passiert ist und was liegen geblieben ist —
inklusive Grund.

---

## Selbsttest

Die Erkennung des Seriennamens aus Datei- und Ordnernamen ist durch einen
Selbsttest mit realen Namen abgesichert:

```bash
python mediathek_downloader.py --selftest
```

Nach Änderungen an den Erkennungsmustern immer ausführen — sonst kann eine
kleine Regex-Änderung stillschweigend die halbe Bibliothek umgruppieren.

---

## Als .exe bauen

```bash
pip install pyinstaller
pyinstaller "Mediathek Downloader.spec" --noconfirm
```

---

## Hinweise

Das Programm lädt ausschließlich frei zugängliche Inhalte der öffentlich-recht­
lichen Mediatheken. Beachte die Nutzungsbedingungen der jeweiligen Anbieter
und die Verfügbarkeitsfristen.

Die Metadaten stammen von TheTVDB, TheMovieDB, Trakt.tv, TVmaze und OMDb —
bitte deren Nutzungsbedingungen beachten.
