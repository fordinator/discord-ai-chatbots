// static/script.js

document.addEventListener('DOMContentLoaded', () => {
    // --- STATE MANAGEMENT ---
    let session_id = null;

    // --- DOM ELEMENTS ---
    const storyLog = document.getElementById('story-log');
    const actionButtons = document.getElementById('action-buttons');
    const actionInput = document.getElementById('action-input');
    const actionForm = document.getElementById('action-form');
    const charCreationArea = document.getElementById('character-creation');
    const gameInputArea = document.getElementById('game-input-area');
    const charCreatorForm = document.getElementById('char-creator-form');
    const consentCheckbox = document.getElementById('consent-checkbox');
    const startGameBtn = document.getElementById('start-game-btn');
    const statusDisplay = document.getElementById('status-display');
    const inputPrompt = document.getElementById('input-prompt');

    // --- UTILITY FUNCTIONS ---
    function addLogEntry(className, htmlContent) {
        const entry = document.createElement('div');
        entry.className = `log-entry ${className}`;
        entry.innerHTML = htmlContent.replace(/\n/g, '<br>'); // Sanitize newlines
        storyLog.appendChild(entry);
        storyLog.scrollTop = storyLog.scrollHeight;
    }

    function clearActionButtons() {
        actionButtons.innerHTML = '';
    }

    function createActionButton(text, id, className = '') {
        const button = document.createElement('button');
        button.textContent = text;
        button.dataset.id = id;
        if(className) button.classList.add(className);
        button.addEventListener('click', () => handleButtonAction(id));
        actionButtons.appendChild(button);
    }
    
    function updateStatusDisplay(data) {
        if (!data) return;
        let html = '';
        if (data.turn > 0 && data.turn_limit) {
            html += `<span class="status-item">Turn: ${data.turn} / ${data.turn_limit}</span>`;
        }
        if (data.fate_pool !== undefined) {
            html += `<span class="status-item">Fate Pool: ${data.fate_pool}</span>`;
        }
        
        let statsHtml = '';
        if (data.stats) {
            statsHtml += '<div class="stat-block-grid">';
            for (const [key, value] of Object.entries(data.stats)) {
                statsHtml += `<div>${key}: ${value > 0 ? '+' : ''}${value}</div>`;
            }
            statsHtml += '</div>';
        }

        let combatStatsHtml = '';
        if (data.combat_stats) {
            combatStatsHtml += '<div class="stat-block-grid combat-stats">';
             for (const [key, value] of Object.entries(data.combat_stats)) {
                combatStatsHtml += `<div>${key.replace(/_/g, ' ')}: ${value > 0 ? '+' : ''}${value}</div>`;
            }
            combatStatsHtml += '</div>';
        }

        statusDisplay.innerHTML = `<div class="status-bar">${html}</div>${statsHtml}${combatStatsHtml}`;
    }

    // --- EVENT HANDLERS ---
    consentCheckbox.addEventListener('change', () => {
        startGameBtn.disabled = !consentCheckbox.checked;
    });

    charCreatorForm.addEventListener('submit', async (e) => {
        e.preventDefault();
        setInputsDisabled(true);
        const stats = {
            STR: parseInt(document.getElementById('str').value),
            DEX: parseInt(document.getElementById('dex').value),
            CON: parseInt(document.getElementById('con').value),
            INT: parseInt(document.getElementById('int').value),
            WIS: parseInt(document.getElementById('wis').value),
            CHA: parseInt(document.getElementById('cha').value),
        };

        try {
            const response = await fetch('/api/start_game', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ consent_given: true, stats: stats })
            });
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
            const data = await response.json();
            
            session_id = data.session_id;
            charCreationArea.style.display = 'none';
            // --- CHANGED ---
            // Directly call the main response handler to ensure consistent UI.
            processApiResponse(data); 

        } catch (error) {
            console.error('Failed to start game:', error);
            addLogEntry('error', 'Could not start the game. Please try again later.');
            setInputsDisabled(false); // Re-enable on error
        }
    });

    actionForm.addEventListener('submit', (e) => {
        e.preventDefault();
        const text = actionInput.value.trim();
        if (text) {
            addLogEntry('user', `&gt; ${text}`);
            handleTextAction(text);
            actionInput.value = '';
        }
    });
    
    async function handleTextAction(text) {
        if (!session_id) return;
        setInputsDisabled(true);
        gameInputArea.style.display = 'none';
        const response = await postAction({ action_type: 'text', value: text });
        processApiResponse(response);
    }
    
    async function handleButtonAction(buttonId) {
        if (!session_id) return;
        setInputsDisabled(true);
        const response = await postAction({ action_type: 'button', value: buttonId });
        processApiResponse(response);
    }

    async function postAction(body) {
        try {
            const response = await fetch('/api/game_action', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ session_id, ...body })
            });
            if (!response.ok) throw new Error(`HTTP error! status: ${response.status}`);
            return await response.json();
        } catch (error) {
            console.error('Action failed:', error);
            addLogEntry('error', 'An error occurred. Please try again.');
            setInputsDisabled(false);
            return null;
        }
    }

    function processApiResponse(data) {
        if (!data) {
            setInputsDisabled(false);
            return;
        }

        clearActionButtons();
        updateStatusDisplay(data);

        if (data.message) {
            addLogEntry('system', data.message);
        }
        if (data.roll_summary) {
            addLogEntry('roll-summary', data.roll_summary);
        }
        if (data.error) {
            addLogEntry('error', data.error);
        }

        if (data.buttons) {
            data.buttons.forEach(btn => createActionButton(btn.text, btn.id));
        }

        if (data.action === 'listen_for_stream') {
            listenToStream();
        } else if (data.state === 'IDLE') {
            gameInputArea.style.display = 'none';
            createActionButton('STR', 'STR');
            createActionButton('DEX', 'DEX');
            createActionButton('CON', 'CON');
            createActionButton('INT', 'INT');
            createActionButton('WIS', 'WIS');
            createActionButton('CHA', 'CHA');
            if (data.fate_pool > 0) {
                 createActionButton(`Use Fate (${data.fate_pool})`, 'USE_FATE', 'secondary');
            }
            setInputsDisabled(false);
        // --- CHANGED ---
        // Added AWAITING_DESCRIPTION to this condition to show the text box.
        } else if (data.state === 'AWAITING_DESCRIPTION' || data.state === 'AWAITING_STAT_ACTION_INPUT' || data.state === 'AWAITING_FV_SPEND' || data.state === 'AWAITING_GEAR_DESCRIPTION') {
            gameInputArea.style.display = 'flex';
            inputPrompt.textContent = data.message.split('\n')[0]; // Use first line of message as prompt
            setInputsDisabled(false);
            actionInput.focus();
        } else {
            gameInputArea.style.display = 'none';
            setInputsDisabled(false);
        }
    }
    
    function setInputsDisabled(disabled) {
        actionInput.disabled = disabled;
        actionForm.querySelector('button').disabled = disabled;
        actionButtons.querySelectorAll('button').forEach(b => b.disabled = disabled);
    }
    
    function listenToStream() {
        addLogEntry('dm-stream', '<span class="blinking-cursor"></span>');
        const eventSource = new EventSource(`/api/stream/${session_id}`);
        const streamEntry = storyLog.querySelector('.dm-stream:last-child');
        let fullContent = '';

        eventSource.onmessage = function(event) {
            const data = JSON.parse(event.data);
            if (data.type === 'chunk') {
                fullContent += data.content;
                streamEntry.innerHTML = fullContent.replace(/\n/g, '<br>') + '<span class="blinking-cursor"></span>';
                storyLog.scrollTop = storyLog.scrollHeight;
            } else if (data.type === 'end') {
                streamEntry.innerHTML = data.content.replace(/\n/g, '<br>');
                eventSource.close();
                // After story streams, poll for the updated state
                postAction({ action_type: 'button', value: 'refresh_state' }).then(processApiResponse);
            } else if (data.type === 'error') {
                addLogEntry('error', data.content);
                eventSource.close();
                setInputsDisabled(false);
            }
        };

        eventSource.onerror = function(err) {
            console.error("EventSource failed:", err);
            addLogEntry('error', 'Connection to the storyteller was lost.');
            eventSource.close();
            setInputsDisabled(false);
        };
    }
});